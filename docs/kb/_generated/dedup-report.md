# ArkLib dedup-candidate report

Generated from `docs/kb/_generated/declarations.json`. **Eyeball, do not auto-rewrite.** The point is to surface name collisions and doc-string overlap that *might* indicate an opportunity to consolidate.

## Stats

- `ArkLib` — 2256 files, 28949 declarations

## Same short-name across multiple files (1242 groups)

Each group lists declarations sharing a short name across ≥2 files. Most are legitimate (overloaded interface, paper-shape vs general form), but the list is the right anchor to look for duplicates.

### `reduction` (13 declarations, 12 files)

- `def KZG.CommitmentScheme.reduction` [ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean:115](../../../ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean#L115) — The reduction breaking ARSDH using a successful function-binding adversary. The reduction follows th
- `def CheckClaim.reduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:56](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L56) — The reduction for the `CheckClaim` reduction.
- `def DoNothing.reduction` [ArkLib/ProofSystem/Component/DoNothing.lean:44](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L44) — The reduction for the `DoNothing` reduction. - Prover simply returns the statement and witness. - Ve
- `def NoInteraction.reduction` [ArkLib/ProofSystem/Component/NoInteraction.lean:62](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L62) — The no-interaction reduction can be specified by a tuple of functions: - `mapStmt : StmtIn → OracleC
- `def ReduceClaim.reduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:59](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L59) — The reduction for the `ReduceClaim` reduction.
- `def SendWitness.reduction` [ArkLib/ProofSystem/Component/SendWitness.lean:78](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L78) — (no docstring)
- `def Fri.Spec.reduction` [ArkLib/ProofSystem/Fri/Spec/General.lean:107](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L107) — (no docstring)
- `inductive reduction` [ArkLib/ProofSystem/Logup/Security/BridgeAndAppendResiduals.lean:36](../../../ArkLib/ProofSystem/Logup/Security/BridgeAndAppendResiduals.lean#L36) — (no docstring)
- `def Sumcheck.Spec.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:168](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L168) — The sum-check protocol as a reduction
- `def Sumcheck.Spec.SingleRound.Simple.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:642](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L642) — The reduction for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1377](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1377) — The sum-check reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Spec.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:499](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L499) — Honest reduction for Construction 6.2: the package `{prover, verifier}` over the bundled-input `Redu
- `def ToyProblem.SimplifiedIOR.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:168](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L168) — Honest reduction for Construction 6.9.

### `agree` (13 declarations, 11 files)

- `def CodeGeometry.agree` [ArkLib/Data/CodingTheory/CodeGeometry.lean:38](../../../ArkLib/Data/CodingTheory/CodeGeometry.lean#L38) — (no docstring)
- `def ArkLib.JohnsonBound.agree` [ArkLib/Data/CodingTheory/JohnsonBound/ListSize.lean:54](../../../ArkLib/Data/CodingTheory/JohnsonBound/ListSize.lean#L54) — The number of coordinates on which `c` and `w` agree.
- `def ProximityGap.WeightedAgreement.agree` [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean:236](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean#L236) — Relative `μ`-agreement between words `u` and `v`.
- `def ConcretePin.agree` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarConcretePinF17.lean:85](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarConcretePinF17.lean#L85) — Agreement count of a line `(b, c)` with a word `w` over the domain `G`.
- `def R10ExactDelta.agree` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean:90](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean#L90) — Agreement of `w` with the line `(b,c)`: number of domain points `x ∈ G` (with paired word value `wx
- `def R11DeltaTable.Row1.agree` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:122](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L122) — Agreement of `w₁` with the quadratic `(b,c,d)` on `G`.
- `def R11DeltaTable.Row2.agree` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:182](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L182) — Agreement of `w₂` with the line `(b,c)` on `G`.
- `def R11DeltaTable.Row3.agree` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:239](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L239) — Agreement of `w₃` with the line `(b,c)` on `G`.
- `def R14GS.agree` [ArkLib/Data/CodingTheory/ProximityGap/GSPipelineAssembly.lean:79](../../../ArkLib/Data/CodingTheory/ProximityGap/GSPipelineAssembly.lean#L79) — Number of evaluation points where `f` agrees with the received word `w`.
- `def ArkLib.CodingTheory.FourthMoment.agree` [ArkLib/Data/CodingTheory/ProximityGap/JohnsonFourthMomentNoGo.lean:84](../../../ArkLib/Data/CodingTheory/ProximityGap/JohnsonFourthMomentNoGo.lean#L84) — Number of coordinates on which `x` and `y` agree (same convention as `JohnsonSimplexBound`).
- `def ArkLib.CodingTheory.JohnsonSimplex.agree` [ArkLib/Data/CodingTheory/ProximityGap/JohnsonSimplexBound.lean:35](../../../ArkLib/Data/CodingTheory/ProximityGap/JohnsonSimplexBound.lean#L35) — Number of coordinates on which `x` and `y` agree.
- `def ArkLib.CodingTheory.ListThresholdWellDefined.agree` [ArkLib/Data/CodingTheory/ProximityGap/ListThresholdWellDefined.lean:41](../../../ArkLib/Data/CodingTheory/ProximityGap/ListThresholdWellDefined.lean#L41) — The agreement count of a codeword `c` with a received word `w`.
- `def ArkLib.ProximityGap.RSPrizeDataPoint.agree` [ArkLib/Data/CodingTheory/ProximityGap/RSListSizeDataPoint.lean:52](../../../ArkLib/Data/CodingTheory/ProximityGap/RSListSizeDataPoint.lean#L52) — Number of coordinates on which the received word `w` agrees with codeword `(a0, a1)`.

### `pSpec` (13 declarations, 11 files)

- `def RandomQuery.pSpec` [ArkLib/ProofSystem/Component/RandomQuery.lean:56](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L56) — (no docstring)
- `def SendClaim.pSpec` [ArkLib/ProofSystem/Component/SendClaim.lean:32](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L32) — (no docstring)
- `def SendWitness.pSpec` [ArkLib/ProofSystem/Component/SendWitness.lean:54](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L54) — (no docstring)
- `def Fri.Spec.FoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:349](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L349) — Each round of the FRI protocol begins with the verifier sending a random field element as the challe
- `def Fri.Spec.FinalFoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:666](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L666) — The final folding round of the FRI protocol begins with the verifier sending a random field element
- `def Fri.Spec.QueryRound.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:977](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L977) — (no docstring)
- `def Logup.pSpec` [ArkLib/ProofSystem/Logup/Protocol.lean:80](../../../ArkLib/ProofSystem/Logup/Protocol.lean#L80) — Protocol 2 transcript shape: the outer LogUp messages followed by ArkLib's generic sumcheck.
- `def StirIOP.Round.pSpec` [ArkLib/ProofSystem/Stir/RoundProtocol.lean:60](../../../ArkLib/ProofSystem/Stir/RoundProtocol.lean#L60) — The protocol spec of one STIR fold round: the verifier first sends a folding challenge in `F` (`V_to
- `def Sumcheck.Spec.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:125](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L125) — The protocol specification for the general sum-check protocol, which is the composition of the singl
- `def Sumcheck.Spec.SingleRound.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L149) — The protocol specification for a single round of sum-check. Has the form `⟨!v[.P_to_V, .V_to_P], !v[
- `def ToyProblem.Spec.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:132](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L132) — Protocol specification for Construction 6.2: three rounds, in the order V → P  (γ : F)            --
- `def ToyProblem.SimplifiedIOR.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:108](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L108) — Protocol specification for Construction 6.9: a single `V → P` round sending the combination randomne
- `def WhirIOP.FoldRound.pSpec` [ArkLib/ProofSystem/Whir/FoldRound.lean:149](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L149) — Protocol spec: the verifier sends a fold challenge `α : F`, then the prover sends the folded oracle

### `oracleVerifier` (11 declarations, 10 files)

- `def CheckClaim.oracleVerifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:250](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L250) — The oracle verifier for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleVerifier` [ArkLib/ProofSystem/Component/DoNothing.lean:106](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L106) — The oracle verifier for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleVerifier` [ArkLib/ProofSystem/Component/RandomQuery.lean:88](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L88) — The oracle verifier simply returns the challenge, and performs no checks.
- `def ReduceClaim.oracleVerifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:260](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L260) — The oracle verifier for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleVerifier` [ArkLib/ProofSystem/Component/SendClaim.lean:67](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L67) — The verifier checks that the relationship `rel oldStmt newStmt` holds. It has access to the original
- `def SendSingleWitness.oracleVerifier` [ArkLib/ProofSystem/Component/SendWitness.lean:353](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L353) — The oracle verifier for the `SendSingleWitness` oracle reduction. The verifier receives the input st
- `def RingSwitching.BatchingPhase.oracleVerifier` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:196](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L196) — (no docstring)
- `def Sumcheck.Spec.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:158](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L158) — The oracle verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:702](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L702) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1358](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1358) — The oracle verifier for the `i`-th round of the sum-check protocol. Migrated to the new `OracleState
- `def ToyProblem.Spec.oracleVerifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:576](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L576) — Oracle verifier for Construction 6.2. Queries the prover's message `g` once and the two oracle codew

### `OracleStatement` (10 declarations, 10 files)

- `abbrev Interaction.OracleStatement` [ArkLib/Interaction/Oracle/Core.lean:100](../../../ArkLib/Interaction/Oracle/Core.lean#L100) — (no docstring)
- `def BatchedFri.Spec.OracleStatement` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:46](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L46) — An oracle for each batched polynomial.
- `def Binius.BinaryBasefold.OracleStatement` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:835](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L835) — For the `i`-th round of the protocol, there will be oracle statements corresponding to all committed
- `def R1CS.OracleStatement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:48](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L48) — (no docstring)
- `def Fri.Spec.OracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:89](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L89) — For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the beginning
- `abbrev Spartan.Spec.OracleStatement` [ArkLib/ProofSystem/Spartan/Basic.lean:60](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L60) — This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R`
- `def StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:84](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L84) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- `def Sumcheck.Spec.OracleStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:136](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L136) — Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of individual
- `def ToyProblem.Spec.OracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:99](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L99) — Oracle statements of Construction 6.2: the two purported codewords `f₁, f₂ : ι → F`. The verifier on
- `def WhirIOP.OracleStatement` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:146](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L146) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type

### `oracleReduction` (11 declarations, 9 files)

- `def CheckClaim.oracleReduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:258](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L258) — The oracle reduction for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleReduction` [ArkLib/ProofSystem/Component/DoNothing.lean:116](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L116) — The oracle reduction for the `DoNothing` oracle reduction. - Prover simply returns the (non-oracle a
- `def RandomQuery.oracleReduction` [ArkLib/ProofSystem/Component/RandomQuery.lean:106](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L106) — Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction: the input o
- `def ReduceClaim.oracleReduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:277](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L277) — The oracle reduction for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleReduction` [ArkLib/ProofSystem/Component/SendClaim.lean:96](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L96) — Combine the prover and verifier into an oracle reduction. The input has no statement or witness, but
- `def SendSingleWitness.oracleReduction` [ArkLib/ProofSystem/Component/SendWitness.lean:366](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L366) — (no docstring)
- `def Sumcheck.Spec.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:180](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L180) — The sum-check protocol as an oracle reduction
- `def Sumcheck.Spec.SingleRound.Simpler.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:566](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L566) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:721](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L721) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1387](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1387) — The sum-check oracle reduction for the `i`-th round of the sum-check protocol. Migrated to the new `
- `def ToyProblem.Spec.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:608](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L608) — Honest oracle reduction for Construction 6.2: the `OracleProver` / `OracleVerifier` pair packaged as

### `verifier` (11 declarations, 9 files)

- `def CheckClaim.verifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:51](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L51) — The verifier for the `CheckClaim` reduction.
- `def DoNothing.verifier` [ArkLib/ProofSystem/Component/DoNothing.lean:35](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L35) — The verifier for the `DoNothing` reduction.
- `def NoInteraction.verifier` [ArkLib/ProofSystem/Component/NoInteraction.lean:53](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L53) — The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a function
- `def ReduceClaim.verifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:55](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L55) — The verifier for the `ReduceClaim` reduction.
- `def SendWitness.verifier` [ArkLib/ProofSystem/Component/SendWitness.lean:74](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L74) — (no docstring)
- `def Sumcheck.Spec.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L149) — The verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:633](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L633) — The verifier for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1348](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1348) — The verifier for the `i`-th round of the sum-check protocol
- `def Sumcheck.Spec.SingleRound.Unfolded.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1896](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1896) — The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1`
- `def ToyProblem.Spec.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:485](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L485) — Honest verifier for Construction 6.2. Takes the bundled input `(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂
- `def ToyProblem.SimplifiedIOR.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:157](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L157) — Honest verifier for Construction 6.9. Reads `γ` from the transcript and produces the new statement `

### `inputRelation` (11 declarations, 8 files)

- `def BatchedFri.Spec.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/General.lean:67](../../../ArkLib/ProofSystem/BatchedFri/Spec/General.lean#L67) — (no docstring)
- `def BatchedFri.Spec.BatchingRound.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:69](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L69) — (no docstring)
- `def Fri.Spec.inputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:46](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L46) — (no docstring)
- `def Fri.Spec.FoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:283](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L283) — The FRI non-final folding round input relation, with proximity parameter `0 < δ`, for the `i`-th rou
- `def Fri.Spec.FinalFoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:604](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L604) — Input relation for the final folding round, with proximity parameter `0 < δ`. Two conditions (mirror
- `def Fri.Spec.QueryRound.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:956](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L956) — (no docstring)
- `def Logup.inputRelation` [ArkLib/ProofSystem/Logup/Common.lean:264](../../../ArkLib/ProofSystem/Logup/Common.lean#L264) — Semantic input relation for Protocol 2: every lookup-column value occurs in the table range.
- `def Sumcheck.Spec.SingleRound.Simpler.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:338](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L338) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:596](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L596) — (no docstring)
- `def ToyProblem.Spec.inputRelation` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:187](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L187) — The IOR-shaped input relation derived from `ToyProblem.relation` (Definition 6.1). `((v, μ₁, μ₂), (f
- `def WhirIOP.FoldRound.inputRelation` [ArkLib/ProofSystem/Whir/FoldRound.lean:210](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L210) — Input relation: the committed oracle is a codeword of the level-`j` smooth code of degree-budget `M

### `oracleProver` (9 declarations, 8 files)

- `def CheckClaim.oracleProver` [ArkLib/ProofSystem/Component/CheckClaim.lean:237](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L237) — The oracle prover for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleProver` [ArkLib/ProofSystem/Component/DoNothing.lean:101](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L101) — The oracle prover for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleProver` [ArkLib/ProofSystem/Component/RandomQuery.lean:68](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L68) — The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`, a
- `def ReduceClaim.oracleProver` [ArkLib/ProofSystem/Component/ReduceClaim.lean:250](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L250) — The oracle prover for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleProver` [ArkLib/ProofSystem/Component/SendClaim.lean:40](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L40) — The prover takes in the old oracle statement as input, and sends it as the protocol message.
- `def SendWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:269](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L269) — The oracle prover for the `SendWitness` oracle reduction. For each round `i : Fin (FinEnum.card ιw)`
- `def SendSingleWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:337](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L337) — The oracle prover for the `SendSingleWitness` oracle reduction. The prover sends the witness `wit` t
- `def RingSwitching.BatchingPhase.oracleProver` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:148](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L148) — (no docstring)
- `def ToyProblem.Spec.oracleProver` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:528](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L528) — Same as `prover` but exposed at the `OracleProver` signature. The underlying `Prover` is identical (

### `prover` (9 declarations, 8 files)

- `def CheckClaim.prover` [ArkLib/ProofSystem/Component/CheckClaim.lean:40](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L40) — The prover for the `CheckClaim` reduction.
- `def DoNothing.prover` [ArkLib/ProofSystem/Component/DoNothing.lean:31](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L31) — The prover for the `DoNothing` reduction.
- `def NoInteraction.prover` [ArkLib/ProofSystem/Component/NoInteraction.lean:43](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L43) — The prover in a no-interaction reduction can be specified by a tuple of functions: - `mapStmt : Stmt
- `def ReduceClaim.prover` [ArkLib/ProofSystem/Component/ReduceClaim.lean:47](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L47) — The prover for the `ReduceClaim` reduction.
- `def SendWitness.prover` [ArkLib/ProofSystem/Component/SendWitness.lean:64](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L64) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:611](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L611) — The prover in the simple description of a single round of sum-check. Takes in input `target : R` and
- `def Sumcheck.Spec.SingleRound.Unfolded.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1886](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1886) — The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only well-
- `def ToyProblem.Spec.prover` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:441](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L441) — Honest prover for Construction 6.2. After receiving the combination randomness `γ`, the prover sends
- `def ToyProblem.SimplifiedIOR.prover` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:126](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L126) — Honest prover for Construction 6.9. After receiving `γ`, sets the new witness `M_new := M₀ + γ·M₁` a

### `relation` (9 declarations, 8 files)

- `def ArkLib.Lattices.ModuleSIS.relation` [ArkLib/Data/Lattices/ModuleSIS.lean:82](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L82) — The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short, and lies in the k
- `def ConstraintSystem.relation` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:68](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L68) — The underlying set-theoretic relation at a given index.
- `def Lookup.relation` [ArkLib/ProofSystem/ConstraintSystem/Lookup.lean:25](../../../ArkLib/ProofSystem/ConstraintSystem/Lookup.lean#L25) — The lookup relation. Takes in a collection of values and a table, both containers for elements of ty
- `def MemoryChecking.ReadOnly.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:128](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L128) — The read-only memory checking relation. It takes a memory `mem` and a list of read operations `ops`.
- `def MemoryChecking.ReadWrite.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:161](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L161) — The read-write memory checking relation. It takes an initial memory `startMem`, a final memory `fina
- `def Plonk.relation` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:193](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L193) — To define a relation based on the constraint system, we extend it with: - A natural number `ℓ ≤ m` r
- `def R1CS.relation` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:61](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L61) — The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean component-wise
- `abbrev Spartan.Spec.relation` [ArkLib/ProofSystem/Spartan/Basic.lean:68](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L68) — This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨`
- `def ToyProblem.relation` [ArkLib/ProofSystem/ToyProblem/Definitions.lean:78](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean#L78) — **Definition 6.1 of [ABF26]** (toy problem relation `R_C^ℓ`). Given a base code `C ⊆ (ι → F)` (the p

### `outputRelation` (10 declarations, 7 files)

- `def BatchedFri.Spec.BatchingRound.outputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:85](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L85) — (no docstring)
- `def Fri.Spec.outputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:56](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L56) — (no docstring)
- `def Fri.Spec.FoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:312](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L312) — The FRI non-final folding round output relation, with proximity parameter `0 < δ`, for the `i`-th ro
- `def Fri.Spec.FinalFoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:634](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L634) — Output relation for the final folding round. After the final round the prover sends a polynomial in
- `def Fri.Spec.QueryRound.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:964](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L964) — (no docstring)
- `def Logup.outputRelation` [ArkLib/ProofSystem/Logup/Common.lean:299](../../../ArkLib/ProofSystem/Logup/Common.lean#L299) — The full protocol has a trivial final relation: successful verification returns `Unit`.
- `def Sumcheck.Spec.SingleRound.Simpler.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:367](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L367) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:599](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L599) — (no docstring)
- `def ToyProblem.Spec.outputRelation` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:266](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L266) — The IOR-shaped *relaxed* output relation derived from `ToyProblem.relaxedRelation` (Definition 6.3).
- `def WhirIOP.FoldRound.outputRelation` [ArkLib/ProofSystem/Whir/FoldRound.lean:216](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L216) — Output relation: the folded oracle is a codeword of the level-`(j+1)` smooth code of degree-budget `

### `getElem` (7 declarations, 7 files)

- `theorem Array.getElem` [ArkLib/Data/Array/Lemmas.lean:63](../../../ArkLib/Data/Array/Lemmas.lean#L63) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:88](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L88) — Shifting a tracked slot through `eraseIdx` of a different index.
- `theorem DuplexSpongeFS.EagerLazyDS.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:959](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L959) — The `getElem?` position map of `eraseIdx`: deleting index `i` shifts later positions by one, for all
- `lemma DuplexSpongeFS.Sponge316.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:137](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L137) — Shifting a tracked slot through `eraseIdx` of a different index.
- `lemma DuplexSpongeFS.Sponge316.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:88](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L88) — Shifting a tracked slot through `eraseIdx` of a different index.
- `lemma DuplexSpongeFS.Sponge316.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:137](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L137) — Shifting a tracked slot through `eraseIdx` of a different index.
- `theorem DuplexSpongeFS.EagerLazyDS.getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:959](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L959) — The `getElem?` position map of `eraseIdx`: deleting index `i` shifts later positions by one, for all

### `Witness` (6 declarations, 6 files)

- `def BatchedFri.Spec.Witness` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:54](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L54) — The Batched FRI protocol has as witness for each batched polynomial that is supposed to correspond t
- `structure Binius.BinaryBasefold.Witness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:898](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L898) — The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and `Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁'
- `def R1CS.Witness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:51](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L51) — (no docstring)
- `def Fri.Spec.Witness` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:110](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L110) — The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in the
- `abbrev Spartan.Spec.Witness` [ArkLib/ProofSystem/Spartan/Basic.lean:64](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L64) — This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R`
- `def ToyProblem.Spec.Witness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:107](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L107) — Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose encodings are the oracle codeword

### `Statement` (5 declarations, 5 files)

- `def R1CS.Statement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:45](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L45) — (no docstring)
- `def Fri.Spec.Statement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:80](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L80) — For the `i`-th round of the protocol, the input statement is equal to the challenges sent from round
- `abbrev Spartan.Spec.Statement` [ArkLib/ProofSystem/Spartan/Basic.lean:56](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L56) — This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R`
- `structure Sumcheck.Structured.Statement` [ArkLib/ProofSystem/Sumcheck/Structured.lean:197](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L197) — Statement per iterated sumcheck round
- `def ToyProblem.Spec.Statement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:93](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L93) — Input (explicit) statement of Construction 6.2: the linear-constraint vector `v ∈ F^k` and the two c

### `liftComp_optionT_pure` (5 declarations, 5 files)

- `lemma StirIOP.Round3.liftComp_optionT_pure` [ArkLib/ProofSystem/Stir/CheckedFinalBlock.lean:277](../../../ArkLib/ProofSystem/Stir/CheckedFinalBlock.lean#L277) — Spec-lifting an `OptionT`-level `pure` is `pure` (definitional; the WHIR `CheckedVerifier` helper).
- `lemma Whir302Checked.liftComp_optionT_pure` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:913](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L913) — Spec-lifting an `OptionT`-level `pure` is `pure` (definitional).
- `lemma Whir302.liftComp_optionT_pure` [ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean:66](../../../ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean#L66) — Spec-lifting an `OptionT`-level `pure` is `pure` (definitional).
- `lemma Whir302RBR.liftComp_optionT_pure` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:413](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L413) — Spec-lifting an `OptionT`-level `pure` is `pure` (definitional).
- `lemma Fri.Spec.Completeness.liftComp_optionT_pure` [ArkLib/ToMathlib/FriCompletePerRound.lean:112](../../../ArkLib/ToMathlib/FriCompletePerRound.lean#L112) — Spec-lifting an `OptionT`-level `pure` is `pure` (definitional); cf. the WHIR sibling `liftComp_opti

### `oracleVerifier_rbrKnowledgeSoundness` (5 declarations, 5 files)

- `theorem DoNothing.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:132](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L132) — The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound.
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomQuery.lean:351](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L351) — The `RandomQuery` oracle reduction is round-by-round knowledge sound. The key fact governing the sou
- `theorem ReduceClaim.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:489](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L489) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/RbrKnowledgeSoundnessOracle.lean:168](../../../ArkLib/ProofSystem/Sumcheck/Spec/RbrKnowledgeSoundnessOracle.lean#L168) — **The full multi-round sum-check ORACLE verifier is round-by-round knowledge sound** on the canonica
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1220](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1220) — Round-by-round knowledge soundness for the oracle verifier

### `pow_half_eq_neg_one` (5 declarations, 5 files)

- `lemma ArkLib.ProximityGap.KKH26.pow_half_eq_neg_one` [ArkLib/Data/CodingTheory/ProximityGap/KKH26SumsOfRootsOfUnity.lean:444](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26SumsOfRootsOfUnity.lean#L444) — `g^{2^{m-1}} = −1` for a primitive `2^m`-th root of unity in a prime field.
- `lemma LamLeungTwoPow.pow_half_eq_neg_one` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean:38](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean#L38) — A primitive `2^(m+1)`-th root of unity has `ζ^(2^m) = −1`.
- `theorem R12.pow_half_eq_neg_one` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean:165](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean#L165) — For a primitive `2^m`-th root of unity `ζ` (`m ≥ 1`), `ζ^{2^{m-1}} = -1`: `ζ^{2^{m-1}}` is a primiti
- `theorem Round29IteratedLift.pow_half_eq_neg_one` [ArkLib/Data/CodingTheory/ProximityGap/RigidityIterated2kLift.lean:369](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityIterated2kLift.lean#L369) — For `ζ` primitive `2^m`-th (`m ≥ 1`), the half-order power is `−1`.
- `theorem ArkLib.ProximityGap.Round3SubgroupSumsetDirect.pow_half_eq_neg_one` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupSumsetThreePowUpper.lean:79](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupSumsetThreePowUpper.lean#L79) — For a primitive `2N`-th root of unity `ζ` (`N ≥ 1`), `ζ^N = -1`: `ζ^N` is a primitive square root of

### `OStmtIn` (5 declarations, 4 files)

- `def RandomQuery.OStmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:36](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L36) — (no docstring)
- `def Logup.OStmtIn` [ArkLib/ProofSystem/Logup/Common.lean:241](../../../ArkLib/ProofSystem/Logup/Common.lean#L241) — Input oracle statements: the table `t` and lookup columns `fᵢ`, as multilinear oracles.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:336](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L336) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:591](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L591) — (no docstring)
- `def WhirIOP.FoldRound.OStmtIn` [ArkLib/ProofSystem/Whir/FoldRound.lean:135](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L135) — The oracle message type for this round: the single committed codeword as a function on the relevant

### `OStmtOut` (5 declarations, 4 files)

- `def RandomQuery.OStmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:37](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L37) — (no docstring)
- `def Logup.OStmtOut` [ArkLib/ProofSystem/Logup/Common.lean:290](../../../ArkLib/ProofSystem/Logup/Common.lean#L290) — Output oracle statements for the full LogUp protocol.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:365](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L365) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:594](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L594) — (no docstring)
- `def WhirIOP.FoldRound.OStmtOut` [ArkLib/ProofSystem/Whir/FoldRound.lean:138](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L138) — (no docstring)

### `StmtIn` (5 declarations, 4 files)

- `def RandomQuery.StmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:33](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L33) — (no docstring)
- `structure Logup.StmtIn` [ArkLib/ProofSystem/Logup/Common.lean:233](../../../ArkLib/ProofSystem/Logup/Common.lean#L233) — Public parameter assumptions for Protocol 2. The paper fixes a finite field with characteristic larg
- `def Sumcheck.Spec.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:137](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L137) — The input statement for the (full) sum-check protocol, which contains only the target sum value
- `def Sumcheck.Spec.SingleRound.Simpler.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:335](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L335) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:585](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L585) — (no docstring)

### `oracleReduction_perfectCompleteness` (5 declarations, 4 files)

- `theorem DoNothing.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:126](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L126) — The `DoNothing` oracle reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/OracleCompletenessThreaded.lean:80](../../../ArkLib/ProofSystem/Sumcheck/Spec/OracleCompletenessThreaded.lean#L80) — **Per-round oracle perfect completeness.** The `i`-th-round oracle reduction `SingleRound.oracleRedu
- `theorem Sumcheck.Spec.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/OracleCompletenessThreaded.lean:117](../../../ArkLib/ProofSystem/Sumcheck/Spec/OracleCompletenessThreaded.lean#L117) — **Full multi-round sum-check perfect completeness (oracle level) — without the false bridge.** Assem
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1033](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1033) — Perfect completeness for the oracle reduction
- `theorem ToyProblem.Spec.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:945](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L945) — **Honest completeness for Construction 6.2** (protocol-level form). The honest oracle reduction is p

### `reduction_perfectCompleteness` (5 declarations, 4 files)

- `theorem DoNothing.reduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:52](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L52) — The `DoNothing` reduction satisfies perfect completeness for any relation.
- `theorem Fri.Spec.Completeness.reduction_perfectCompleteness` [ArkLib/ProofSystem/Fri/Spec/Completeness.lean:113](../../../ArkLib/ProofSystem/Fri/Spec/Completeness.lean#L113) — **Brick D — composed FRI reduction perfect completeness.** The honest FRI protocol is perfectly comp
- `theorem Sumcheck.Spec.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/Completeness.lean:87](../../../ArkLib/ProofSystem/Sumcheck/Spec/Completeness.lean#L87) — **Full multi-round sum-check perfect completeness (`Reduction` level).** Assembled from the per-roun
- `theorem Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:742](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L742) — Perfect completeness for the (non-oracle) reduction
- `theorem Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1785](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1785) — (no docstring)

### `agreeCount` (4 declarations, 4 files)

- `def ArkLib.CodingTheory.Round4InteriorList.agreeCount` [ArkLib/Data/CodingTheory/ProximityGap/InteriorListCountBridge.lean:199](../../../ArkLib/Data/CodingTheory/ProximityGap/InteriorListCountBridge.lean#L199) — The agreement count (number of coordinates where two words coincide).
- `def ArkLib.CodingTheory.CapacityLowerSharpen.agreeCount` [ArkLib/Data/CodingTheory/ProximityGap/ListCapacityFieldIndependent.lean:185](../../../ArkLib/Data/CodingTheory/ProximityGap/ListCapacityFieldIndependent.lean#L185) — The agreement count (number of coordinates where two words coincide).
- `def R15MCAGap.agreeCount` [ArkLib/Data/CodingTheory/ProximityGap/MCABadScalarSpreadBridge.lean:59](../../../ArkLib/Data/CodingTheory/ProximityGap/MCABadScalarSpreadBridge.lean#L59) — Number of coordinates on which the word `w` agrees with the word `c`.
- `def RSDeltaStar.agreeCount` [ArkLib/Data/CodingTheory/ProximityGap/RSAveragingDeltaStarUpper.lean:145](../../../ArkLib/Data/CodingTheory/ProximityGap/RSAveragingDeltaStarUpper.lean#L145) — Number of evaluation points where the codeword `tupleToPoly c` agrees with the word `w`.

### `agreeSet` (4 declarations, 4 files)

- `def ProximityPrizeCA.agreeSet` [ArkLib/Data/CodingTheory/ProximityCA.lean:35](../../../ArkLib/Data/CodingTheory/ProximityCA.lean#L35) — The agreement set of two words.
- `def ConcretePin.agreeSet` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarConcretePinF17.lean:169](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarConcretePinF17.lean#L169) — The agreement set of a line `(b, c)` with `w` inside `G`.
- `def LinePairCooccurrence.agreeSet` [ArkLib/Data/CodingTheory/ProximityGap/LinePairCooccurrenceBound.lean:57](../../../ArkLib/Data/CodingTheory/ProximityGap/LinePairCooccurrenceBound.lean#L57) — Coordinates where `u` and `v` agree.
- `def R15Bracket.agreeSet` [ArkLib/Data/CodingTheory/ProximityGap/ScaleBracketFull.lean:180](../../../ArkLib/Data/CodingTheory/ProximityGap/ScaleBracketFull.lean#L180) — The agreement set of two words.

### `disagreementSet` (4 declarations, 4 files)

- `def disagreementSet` [ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean#L63) — The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁. Specialisation of the canonical `Code.disagr
- `def Binius.BinaryBasefold.disagreementSet` [ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean:464](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean#L464) — Disagreement set Δ : The set of points where two functions disagree. For functions f^(i) and g^(i),
- `def Quotienting.disagreementSet` [ArkLib/ProofSystem/Stir/Quotienting.lean:121](../../../ArkLib/ProofSystem/Stir/Quotienting.lean#L121) — We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S such that
- `def BlockRelDistance.disagreementSet` [ArkLib/ProofSystem/Whir/BlockRelDistance.lean:104](../../../ArkLib/ProofSystem/Whir/BlockRelDistance.lean#L104) — Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then the (i,k)

### `fiber` (4 declarations, 4 files)

- `def AveragingCrossover.fiber` [ArkLib/Data/CodingTheory/ProximityGap/AveragingFiberConservation.lean:81](../../../ArkLib/Data/CodingTheory/ProximityGap/AveragingFiberConservation.lean#L81) — The fiber of `Φ` over a target tuple `y`, restricted to `a`-subsets.
- `def ArkLib.ProximityGap.Rigidity.fiber` [ArkLib/Data/CodingTheory/ProximityGap/CosetExactCount.lean:45](../../../ArkLib/Data/CodingTheory/ProximityGap/CosetExactCount.lean#L45) — (no docstring)
- `def Round25General.fiber` [ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean#L60) — The index fiber of `A` at `j`.
- `def ArkLib.ProximityGap.Round5SecondMoment.fiber` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPigeonholeManyTargets.lean:96](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPigeonholeManyTargets.lean#L96) — The `target`-fiber `A_target = { S ∈ powersetCard a G : ∑_{x∈S} x = target }`, whose card is `subset

### `honestTranscriptDist_oracleReduction_evalDist` (4 declarations, 4 files)

- `theorem RandomQuery.honestTranscriptDist_oracleReduction_evalDist` [ArkLib/ProofSystem/Component/RandomQuery.lean:212](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L212) — The honest transcript distribution for `RandomQuery` is definitionally the simulator distribution.
- `theorem ReduceClaim.honestTranscriptDist_oracleReduction_evalDist` [ArkLib/ProofSystem/Component/ReduceClaim.lean:372](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L372) — The honest transcript distribution for the plain `ReduceClaim` oracle reduction is the deterministic
- `theorem SendClaim.honestTranscriptDist_oracleReduction_evalDist` [ArkLib/ProofSystem/Component/SendClaim.lean:254](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L254) — The honest transcript distribution for `SendClaim` is exactly the simulator distribution, because th
- `theorem SendSingleWitness.honestTranscriptDist_oracleReduction_evalDist` [ArkLib/ProofSystem/Component/SendWitness.lean:438](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L438) — The honest transcript distribution for `SendSingleWitness` is the deterministic one-message transcri

### `instOracleVerifierAppendCoherent` (4 declarations, 4 files)

- `instance RandomQuery.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/Component/RandomQuery.lean:112](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L112) — (no docstring)
- `instance SendSingleWitness.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/Component/SendWitness.lean:372](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L372) — (no docstring)
- `instance RingSwitching.BatchingPhase.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:239](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L239) — The batching-phase oracle verifier passes every output oracle through to the unchanged input oracle
- `instance Sumcheck.Spec.SingleRound.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1365](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1365) — The `i`-th-round oracle verifier routes its (single) output oracle to the (unchanged) input oracle (

### `isIntegral_of_pow_eq_one` (4 declarations, 4 files)

- `lemma CRTPacketMinpoly.isIntegral_of_pow_eq_one` [ArkLib/Data/CodingTheory/ProximityGap/CRTPacketMinpoly.lean:54](../../../ArkLib/Data/CodingTheory/ProximityGap/CRTPacketMinpoly.lean#L54) — Roots of unity are integral over any base field of the ambient field.
- `lemma CoprimePacketMinpoly.isIntegral_of_pow_eq_one` [ArkLib/Data/CodingTheory/ProximityGap/CoprimePacketMinpoly.lean:42](../../../ArkLib/Data/CodingTheory/ProximityGap/CoprimePacketMinpoly.lean#L42) — (no docstring)
- `lemma DeBruijnLamLeungSmallWeights.isIntegral_of_pow_eq_one` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnLamLeungSmallWeights.lean:109](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnLamLeungSmallWeights.lean#L109) — Roots of unity are integral over ℚ.
- `lemma ThreadSplit.isIntegral_of_pow_eq_one` [ArkLib/Data/CodingTheory/ProximityGap/ThreadSplit.lean:64](../../../ArkLib/Data/CodingTheory/ProximityGap/ThreadSplit.lean#L64) — Roots of unity are integral over any base field of the ambient field.

### `oracleReduction_isHVZK` (4 declarations, 4 files)

- `theorem DoNothing.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:194](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L194) — The `DoNothing` oracle reduction has an explicit perfect-HVZK simulator for any oracle-input relatio
- `theorem RandomQuery.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:240](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L240) — `RandomQuery` has an explicit perfect-HVZK simulator as an oracle reduction.
- `theorem ReduceClaim.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:423](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L423) — The plain `ReduceClaim` oracle reduction has an explicit perfect-HVZK simulator for any input relati
- `theorem SendClaim.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:285](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L285) — `SendClaim` has an explicit perfect-HVZK simulator as an oracle reduction.

### `oracleReduction_isStatHVZK` (4 declarations, 4 files)

- `theorem DoNothing.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:202](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L202) — The `DoNothing` oracle reduction has statistical HVZK for any oracle-input relation and error budget
- `theorem RandomQuery.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:248](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L248) — `RandomQuery` has statistical HVZK at every error budget as an oracle reduction.
- `theorem ReduceClaim.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:434](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L434) — The plain `ReduceClaim` oracle reduction has statistical HVZK for any input relation and error budge
- `theorem SendClaim.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:295](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L295) — `SendClaim` has statistical HVZK at every error budget as an oracle reduction.

### `oracleReduction_perfectHVZK` (4 declarations, 4 files)

- `theorem DoNothing.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:176](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L176) — The `DoNothing` oracle reduction is perfectly HVZK for any oracle-input relation.
- `theorem RandomQuery.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:221](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L221) — `RandomQuery` is perfectly HVZK as an oracle reduction: it has no private witness, and the single ve
- `theorem ReduceClaim.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:400](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L400) — The plain `ReduceClaim` oracle reduction is perfectly HVZK for any input relation: it has no message
- `theorem SendClaim.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:264](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L264) — `SendClaim` is perfectly HVZK as an oracle reduction for any input relation: the protocol has no pri

### `oracleReduction_statisticalHVZK` (4 declarations, 4 files)

- `theorem DoNothing.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:185](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L185) — The `DoNothing` oracle reduction is statistically HVZK for any oracle-input relation and error budge
- `theorem RandomQuery.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:231](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L231) — Perfect HVZK implies statistical HVZK for `RandomQuery` at every error budget.
- `theorem ReduceClaim.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:412](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L412) — Perfect HVZK implies statistical HVZK for the plain `ReduceClaim` oracle reduction at every error bu
- `theorem SendClaim.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:275](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L275) — Perfect HVZK implies statistical HVZK for `SendClaim` at every error budget.

### `packet_mul_coeff` (4 declarations, 4 files)

- `lemma DeBruijnTwoPrime.packet_mul_coeff` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnTwoPrime.lean:89](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnTwoPrime.lean#L89) — Slices of a geometric-packet multiple: if `deg R < q` then `(Σ_{i<p} X^(iq) · R).coeff (iq + s) = R.
- `lemma LamLeungTwoPow.packet_mul_coeff` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean:1192](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean#L1192) — Slices of a geometric-packet multiple: if `deg R < q` then `(Σ_{i<p} X^{iq} · R).coeff (iq + s) = R.
- `lemma MixedRadixTower.packet_mul_coeff` [ArkLib/Data/CodingTheory/ProximityGap/MixedRadixTower.lean:510](../../../ArkLib/Data/CodingTheory/ProximityGap/MixedRadixTower.lean#L510) — Slices of a geometric-packet multiple: if `deg R < q` then `(Σ_{i<p} X^{iq} · R).coeff (iq + s) = R.
- `lemma PacketCombinationDivisibility.packet_mul_coeff` [ArkLib/Data/CodingTheory/ProximityGap/PacketCombinationDivisibility.lean:132](../../../ArkLib/Data/CodingTheory/ProximityGap/PacketCombinationDivisibility.lean#L132) — Slices of a packet multiple (generic-ring form of `CRTDoubleSlice.packet_slice_coeff`): if `natDegre

### `reduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:71](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L71) — The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the input
- `theorem NoInteraction.reduction_completeness` [ArkLib/ProofSystem/Component/NoInteraction.lean:93](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L93) — Completeness of a no-interaction reduction. **Faithfulness of the hypothesis `hRel`.** `Reduction.ru
- `theorem ReduceClaim.reduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:69](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L69) — The `ReduceClaim` reduction satisfies perfect completeness for any relation.
- `theorem SendWitness.reduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:174](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L174) — The `SendWitness` reduction satisfies perfect completeness.

### `coeffPoly` (4 declarations, 4 files)

- `def GSHasse.coeffPoly` [ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean:135](../../../ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean#L135) — The bivariate polynomial (element of `F[X][Y]`, outer variable `Y`) with coefficient `c' (i, j)` on
- `def GSInterp.coeffPoly` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:98](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L98) — The bivariate polynomial (element of `F[X][Y]`, outer variable `Y`) with coefficient `c' (i, j)` on
- `def R15.coeffPoly` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:105](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L105) — The bivariate polynomial (element of `F[X][Y]`, outer variable `Y`) with coefficient `c' (i, j)` on
- `def R15.coeffPoly` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:105](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L105) — The bivariate polynomial (element of `F[X][Y]`, outer variable `Y`) with coefficient `c' (i, j)` on

### `coeffPoly_coeff` (4 declarations, 4 files)

- `lemma GSHasse.coeffPoly_coeff` [ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean:139](../../../ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean#L139) — (no docstring)
- `lemma GSInterp.coeffPoly_coeff` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:102](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L102) — (no docstring)
- `lemma R15.coeffPoly_coeff` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:109](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L109) — (no docstring)
- `lemma R15.coeffPoly_coeff` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:109](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L109) — (no docstring)

### `exists_ne_zero_map_eq_zero_of_finrank_lt` (4 declarations, 4 files)

- `theorem GSHasse.exists_ne_zero_map_eq_zero_of_finrank_lt` [ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean#L51) — (no docstring)
- `theorem GSInterp.exists_ne_zero_map_eq_zero_of_finrank_lt` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:37](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L37) — (no docstring)
- `theorem R15.exists_ne_zero_map_eq_zero_of_finrank_lt` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L51) — (no docstring)
- `theorem R15.exists_ne_zero_map_eq_zero_of_finrank_lt` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L51) — (no docstring)

### `gsSupport` (4 declarations, 4 files)

- `def GSHasse.gsSupport` [ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean:69](../../../ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean#L69) — Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
- `def GSInterp.gsSupport` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:55](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L55) — Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
- `def R15.gsSupport` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:69](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L69) — Monomial support of the Sudan interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized
- `def R15.gsSupport` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:69](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L69) — Monomial support of the Sudan interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized

### `gsSupport_card` (4 declarations, 4 files)

- `lemma GSHasse.gsSupport_card` [ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean:89](../../../ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean#L89) — Exact count of the monomial support: `∑_{j<D} (D - (k-1)·j)`.
- `lemma GSInterp.gsSupport_card` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:75](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L75) — Exact count of the monomial support: `∑_{j<D} (D - (k-1)·j)`.
- `lemma R15.gsSupport_card` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:82](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L82) — Exact count of the monomial support: `∑_{j<D} (D - (k-1)·j)`.
- `lemma R15.gsSupport_card` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:82](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L82) — Exact count of the monomial support: `∑_{j<D} (D - (k-1)·j)`.

### `gsSupport_weight_lt` (4 declarations, 4 files)

- `lemma GSHasse.gsSupport_weight_lt` [ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean:72](../../../ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean#L72) — (no docstring)
- `lemma GSInterp.gsSupport_weight_lt` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:58](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L58) — (no docstring)
- `lemma R15.gsSupport_weight_lt` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:72](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L72) — (no docstring)
- `lemma R15.gsSupport_weight_lt` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:72](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L72) — (no docstring)

### `natDegree_eval_lt` (4 declarations, 4 files)

- `theorem GSHasse.natDegree_eval_lt` [ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean:381](../../../ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean#L381) — Weighted-degree transfer (as in the multiplicity-1 brick): the support-form weighted degree bound gi
- `theorem GSRootOrder.natDegree_eval_lt` [ArkLib/Data/CodingTheory/ProximityGap/GSRootOrderStep.lean:24](../../../ArkLib/Data/CodingTheory/ProximityGap/GSRootOrderStep.lean#L24) — **Weighted-degree transfer.** If every `Y`-coefficient of `Q : (F[X])[Y]` obeys the `(1, k−1)`-weigh
- `theorem R15.natDegree_eval_lt` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:211](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L211) — Weighted-degree transfer: the univariate restriction `Q(X, f(X))` has degree `< D`.
- `theorem R15.natDegree_eval_lt` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:211](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L211) — Weighted-degree transfer: the univariate restriction `Q(X, f(X))` has degree `< D`.

### `Entry` (4 declarations, 4 files)

- `abbrev DuplexSpongeFS.Sponge316.ForkCounter.Entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L67) — Entry type at `StmtIn := Unit`, `U := UInt8` (sponge geometry `{N := 2, R := 1}` inherited from `Tim
- `abbrev DuplexSpongeFS.Sponge316.ForkCounter.Entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L67) — Entry type at `StmtIn := Unit`, `U := UInt8` (sponge geometry `{N := 2, R := 1}` inherited from `Tim
- `abbrev DuplexSpongeFS.Sponge316.TimePCounter.Entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:73](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L73) — (no docstring)
- `abbrev DuplexSpongeFS.Sponge316.TimePCounter.Entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:73](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L73) — (no docstring)

### `dedup_eq` (4 declarations, 4 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:307](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L307) — The dedup fixpoint of `trcF` is `trcD`: classical choice first erases slot 2 or slot 4, and both bra
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:307](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L307) — The dedup fixpoint of `trcF` is `trcD`: classical choice first erases slot 2 or slot 4, and both bra
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:244](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L244) — The dedup fixpoint of the countermodel trace is `trc'` (erase slot 3, then stop).
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:244](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L244) — The dedup fixpoint of the countermodel trace is `trc'` (erase slot 3, then stop).

### `dedup_eq'` (4 declarations, 4 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L354) — Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L354) — Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L263) — Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L263) — Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.

### `foldl_add_eq_sum` (4 declarations, 4 files)

- `theorem Spartan.Spec.foldl_add_eq_sum` [ArkLib/ProofSystem/Spartan/FirstSumcheckMulVec.lean:36](../../../ArkLib/ProofSystem/Spartan/FirstSumcheckMulVec.lean#L36) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- `theorem Spartan.Spec.foldl_add_eq_sum` [ArkLib/ProofSystem/Spartan/FirstSumcheckZeroEval.lean:39](../../../ArkLib/ProofSystem/Spartan/FirstSumcheckZeroEval.lean#L39) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- `theorem Sumcheck.Spec.SingleRound.foldl_add_eq_sum` [ArkLib/ProofSystem/Sumcheck/Spec/SimpleRoundCoherent.lean:78](../../../ArkLib/ProofSystem/Sumcheck/Spec/SimpleRoundCoherent.lean#L78) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`.
- `theorem Sumcheck.Spec.SingleRound.foldl_add_eq_sum` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRoundFaithful.lean:56](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRoundFaithful.lean#L56) — A left fold that accumulates `acc + g y` over a list equals `acc` plus the list sum of `g`. (Local c

### `prizeRates_le_half` (4 declarations, 4 files)

- `lemma ProximityGap.prizeRates_le_half` [ArkLib/Data/CodingTheory/ProximityGap/Decision.lean:141](../../../ArkLib/Data/CodingTheory/ProximityGap/Decision.lean#L141) — Every prize rate is `≤ 1/2`.
- `lemma ProximityGap.GrandChallengesLattice.prizeRates_le_half` [ArkLib/Data/CodingTheory/ProximityGap/InteriorJ1.lean:626](../../../ArkLib/Data/CodingTheory/ProximityGap/InteriorJ1.lean#L626) — Every ABF26 prize rate is at most `1/2`.
- `lemma ProximityGap.prizeRates_le_half` [ArkLib/Data/CodingTheory/ProximityGap/LDFourRate.lean:208](../../../ArkLib/Data/CodingTheory/ProximityGap/LDFourRate.lean#L208) — Every ABF26 prize rate is at most `1/2`.
- `lemma ProximityGap.prizeRates_le_half` [ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean:363](../../../ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean#L363) — Every prize rate is at most `1/2`.

### `smallSponge` (4 declarations, 4 files)

- `instance DuplexSpongeFS.Sponge314.K1.smallSponge` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:51](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L51) — Tiny sponge geometry: width 2, rate 1, capacity 1 (same as `Lemma516TimePFalse`).
- `instance DuplexSpongeFS.Sponge316.TimePCounter.smallSponge` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:60](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L60) — Tiny sponge geometry: width 2, rate 1, capacity 1 — capacities are single `UInt8`s.
- `instance DuplexSpongeFS.Sponge314.K1.smallSponge` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:51](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L51) — Tiny sponge geometry: width 2, rate 1, capacity 1 (same as `Lemma516TimePFalse`).
- `instance DuplexSpongeFS.Sponge316.TimePCounter.smallSponge` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:60](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L60) — Tiny sponge geometry: width 2, rate 1, capacity 1 — capacities are single `UInt8`s.

### `vsum_two_pos` (4 declarations, 4 files)

- `theorem RingSwitching.vsum_two_pos` [ArkLib/ProofSystem/RingSwitching/WiringInstances.lean:81](../../../ArkLib/ProofSystem/RingSwitching/WiringInstances.lean#L81) — The sumcheck loop (over any `NeZero` number of rounds) has positive length.
- `theorem Spartan.Spec.Bricks.vsum_two_pos` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:291](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L291) — Positivity of two-step round counts.
- `theorem Spartan.Spec.Bricks.vsum_two_pos` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:84](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L84) — Positivity of two-step round counts.
- `theorem Spartan.Spec.Bricks.vsum_two_pos` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:34](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L34) — Positivity of two-step round counts.

### `mem_of_getElem` (4 declarations, 4 files)

- `lemma DuplexSpongeFS.Sponge316.mem_of_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:54](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L54) — Membership from an `getElem?`-hit.
- `lemma DuplexSpongeFS.Sponge316.mem_of_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:157](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L157) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.mem_of_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:54](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L54) — Membership from an `getElem?`-hit.
- `lemma DuplexSpongeFS.Sponge316.mem_of_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:157](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L157) — (no docstring)

### `completeness` (6 declarations, 3 files)

- `abbrev DuplexSpongeFS.NARG.completeness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:59](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L59) — Paper-facing alias for CO25 Section 3.4 completeness.
- `def Reduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:117](../../../ArkLib/OracleReduction/Security/Basic.lean#L117) — A reduction satisfies **completeness** with regards to: - an initialization function `init : ProbCom
- `def OracleReduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:463](../../../ArkLib/OracleReduction/Security/Basic.lean#L463) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:517](../../../ArkLib/OracleReduction/Security/Basic.lean#L517) — (no docstring)
- `def OracleProof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:546](../../../ArkLib/OracleReduction/Security/Basic.lean#L546) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `theorem SendClaim.completeness` [ArkLib/ProofSystem/Component/SendClaim.lean:114](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L114) — (no docstring)

### `soundness` (6 declarations, 3 files)

- `abbrev DuplexSpongeFS.NARG.soundness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:72](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L72) — Paper-facing alias for CO25 Section 3.4 soundness.
- `def Verifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:295](../../../ArkLib/OracleReduction/Security/Basic.lean#L295) — A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input langua
- `def OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:484](../../../ArkLib/OracleReduction/Security/Basic.lean#L484) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:527](../../../ArkLib/OracleReduction/Security/Basic.lean#L527) — (no docstring)
- `def OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:563](../../../ArkLib/OracleReduction/Security/Basic.lean#L563) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.soundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:127](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L127) — State-restoration soundness

### `aStar` (5 declarations, 3 files)

- `def R10ExactDelta.aStar` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean:82](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean#L82) — The crossover threshold `a* = 4` (relative distance `δ* = 1 - 4/16 = 3/4`).
- `def R11DeltaTable.Row1.aStar` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:138](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L138) — The crossover threshold `a* = 5` (`δ* = 1 - 5/16 = 11/16`).
- `def R11DeltaTable.Row2.aStar` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:196](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L196) — The crossover threshold `a* = 3` (`δ* = 1 - 3/8 = 5/8`).
- `def R11DeltaTable.Row3.aStar` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:253](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L253) — The crossover threshold `a* = 3` (`δ* = 1 - 3/8 = 5/8`).
- `def ArkLib.CodingTheory.ListThresholdWellDefined.aStar` [ArkLib/Data/CodingTheory/ProximityGap/ListThresholdWellDefined.lean:157](../../../ArkLib/Data/CodingTheory/ProximityGap/ListThresholdWellDefined.lean#L157) — **The threshold, as a named object:** the minimal agreement demand meeting the budget.

### `ratchet` (5 declarations, 3 files)

- `def DomainSeparator.ratchet` [ArkLib/Data/Hash/DomainSep.lean:255](../../../ArkLib/Data/Hash/DomainSep.lean#L255) — Ratchet the state. Rust interface: ```rust pub fn ratchet(self) -> Self ```
- `def DuplexSponge.ratchet` [ArkLib/Data/Hash/DuplexSponge.lean:612](../../../ArkLib/Data/Hash/DuplexSponge.lean#L612) — ### Ratchet the sponge state for domain separation Algorithm (from Rust implementation): 1. Permute
- `def HashStateWithInstructions.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:217](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L217) — Perform a ratchet operation. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainS
- `def FSVerifierState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:348](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L348) — Signal the end of statement with ratcheting. Rust interface: ```rust pub fn ratchet(&mut self) -> Re
- `def FSProverState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:459](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L459) — Ratchet the protocol state. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainSe

### `Adversary` (4 declarations, 3 files)

- `def AGM.Adversary` [ArkLib/AGM/Basic.lean:468](../../../ArkLib/AGM/Basic.lean#L468) — An adversary in the Algebraic Group Model (AGM) is defined as follows: - It is given knowledge of th
- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.Adversary` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:92](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L92) — A weak-binding adversary outputs two weak openings for the same commitment.
- `abbrev ArkLib.Lattices.SIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:53](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L53) — A search adversary for a SIS-style problem.
- `abbrev ArkLib.Lattices.ModuleSIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:96](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L96) — A Module-SIS adversary.

### `StmtOut` (4 declarations, 3 files)

- `def RandomQuery.StmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:34](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L34) — (no docstring)
- `def Logup.StmtOut` [ArkLib/ProofSystem/Logup/Common.lean:280](../../../ArkLib/ProofSystem/Logup/Common.lean#L280) — The full LogUp protocol returns no additional public data on success.
- `def Sumcheck.Spec.SingleRound.Simpler.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:364](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L364) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:588](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L588) — (no docstring)

### `append` (4 declarations, 3 files)

- `def AGM.GroupRepresentation.append` [ArkLib/AGM/RepresentationLemmas.lean:164](../../../ArkLib/AGM/RepresentationLemmas.lean#L164) — **Representations compose multiplicatively.** Concatenating the bases and exponent vectors of two al
- `def Interaction.Oracle.Spec.append` [ArkLib/Interaction/Oracle/Spec.lean:216](../../../ArkLib/Interaction/Oracle/Spec.lean#L216) — (no docstring)
- `abbrev ProtocolSpec.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:49](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L49) — Appending two `ProtocolSpec`s
- `def ProtocolSpec.FullTranscript.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:160](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L160) — Appending two transcripts for two `ProtocolSpec`s

### `correctness` (4 declarations, 3 files)

- `def Commitment.correctness` [ArkLib/CommitmentScheme/Basic.lean:88](../../../ArkLib/CommitmentScheme/Basic.lean#L88) — A commitment scheme satisfies **correctness** with error `correctnessError` if for all `data : Data`
- `def CommitmentScheme.correctness` [ArkLib/CommitmentScheme/CommitmentScheme.lean:64](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L64) — A commitment scheme satisfies **correctness** with error `correctnessError` if, for every message, t
- `theorem KZG.correctness` [ArkLib/CommitmentScheme/KZG/Correctness.lean:51](../../../ArkLib/CommitmentScheme/KZG/Correctness.lean#L51) — Algebraic correctness of one KZG opening for a coefficient vector.
- `theorem KZG.CommitmentScheme.correctness` [ArkLib/CommitmentScheme/KZG/Correctness.lean:161](../../../ArkLib/CommitmentScheme/KZG/Correctness.lean#L161) — The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

### `drop` (4 declarations, 3 files)

- `def Fin.drop` [ArkLib/Data/Fin/Tuple/Defs.lean:60](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L60) — Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.
- `def ProtocolSpec.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:129](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L129) — Drop the first `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:186](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L186) — (no docstring)
- `def SumcheckDomain.drop` [ArkLib/ProofSystem/Sumcheck/Domain.lean:133](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L133) — Drop the first `j` coordinates, leaving the domain on the remaining `k - j` coordinates: coordinate

### `toFinset` (4 declarations, 3 files)

- `def ReedSolomon.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon.lean:97](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L97) — (no docstring)
- `def Domain.CosetFftDomainClass.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:242](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L242) — (no docstring)
- `abbrev Domain.CosetFftDomain.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:258](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L258) — (no docstring)
- `abbrev Domain.FftDomain.toFinset` [ArkLib/Data/Domain/FftDomain/Defs.lean:126](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L126) — (no docstring)

### `G_card` (3 declarations, 3 files)

- `theorem ArkLib.ProximityGap.AdditiveEnergyFullGroupClosedForm.G_card` [ArkLib/Data/CodingTheory/ProximityGap/AdditiveEnergyFullGroupClosedForm.lean:44](../../../ArkLib/Data/CodingTheory/ProximityGap/AdditiveEnergyFullGroupClosedForm.lean#L44) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyF17.G_card` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyF17.lean:47](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyF17.lean#L47) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupRepCountFiniteFieldCounterexample.G_card` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupRepCountFiniteFieldCounterexample.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupRepCountFiniteFieldCounterexample.lean#L51) — `G` has `8` elements (it is the full subgroup of `8`-th roots of unity, since `8 ∣ 16 = \|F₁₇ˣ\|`).

### `L_subset_code` (3 declarations, 3 files)

- `theorem ArkLib.CodingTheory.TinyInteriorPin.L_subset_code` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:127](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L127) — **Every element of `L` is a Reed–Solomon codeword of degree `< 2`.** This is the non-vacuity witness
- `theorem ArkLib.CodingTheory.TinyInteriorK3.L_subset_code` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:152](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L152) — **Every element of `L` is a Reed–Solomon codeword of degree `< 3`.** Non-vacuity: `L` lives inside t
- `theorem ArkLib.CodingTheory.Round3SmoothF17.L_subset_code` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:162](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L162) — **Every element of `L` is a smooth-domain Reed–Solomon codeword of degree `< 2`.** This is the non-v

### `Message` (3 declarations, 3 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Message` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:122](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L122) — Messages: block vectors over the message row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Message` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:32](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L32) — Messages: column vectors over `Rq Φ`.
- `def ProtocolSpec.Message` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:78](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L78) — The type of the `i`-th message in a protocol specification. This does not distinguish between messag

### `Opening` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.Opening` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:98](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L98) — A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)` (`Decomp`) ext
- `abbrev ArkLib.Lattices.Ajtai.Simple.Opening` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:43](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L43) — The simple Ajtai commitment has no auxiliary opening data.
- `structure Commitment.Opening` [ArkLib/CommitmentScheme/Basic.lean:59](../../../ArkLib/CommitmentScheme/Basic.lean#L59) — The opening protocol used to prove a claimed oracle response for committed data.

### `OutputStatement` (3 declarations, 3 files)

- `abbrev Sumcheck.Spec.OutputStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:131](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L131) — (no docstring)
- `def ToyProblem.Spec.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:112](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L112) — Output statement: the IOR is a yes/no test — accept (return `()`) or short-circuit to `none` via `Op
- `def ToyProblem.SimplifiedIOR.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:72](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L72) — Output statement for C6.9: the new `(v, μ_new)` pair. The constraint count drops from 2 to 1 (a sing

### `Params` (3 declarations, 3 files)

- `structure Poseidon2.Params` [ArkLib/Data/Hash/Poseidon2.lean:412](../../../ArkLib/Data/Hash/Poseidon2.lean#L412) — The parameters determining a Poseidon2 permutation (over the KoalaBear field)
- `structure StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:35](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L35) — **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun
- `structure WhirIOP.Params` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:54](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L54) — ** Per‑round protocol parameters. ** For a fixed depth `M`, the reduction runs `M + 1` rounds. In ro

### `Prover` (4 declarations, 3 files)

- `abbrev Interaction.Oracle.Prover` [ArkLib/Interaction/Oracle/Core.lean:1140](../../../ArkLib/Interaction/Oracle/Core.lean#L1140) — (no docstring)
- `abbrev Interaction.Prover` [ArkLib/Interaction/Reduction.lean:115](../../../ArkLib/Interaction/Reduction.lean#L115) — (no docstring)
- `structure Prover` [ArkLib/OracleReduction/Basic.lean:168](../../../ArkLib/OracleReduction/Basic.lean#L168) — (no docstring)
- `structure Prover` [ArkLib/OracleReduction/Basic.lean:413](../../../ArkLib/OracleReduction/Basic.lean#L413) — The type of honest provers for an interactive reduction with `n` messages. This consists of: - `PrvS

### `PublicParams` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.PublicParams` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:77](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L77) — Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`.
- `abbrev ArkLib.Lattices.Ajtai.Simple.PublicParams` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:29](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L29) — Public parameters: the Ajtai matrix `A`.
- `structure Spartan.PublicParams` [ArkLib/ProofSystem/Spartan/Basic.lean:26](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L26) — The public parameters of the (padded) Spartan protocol. Consists of the number of bits of the R1CS d

### `Reduction` (3 declarations, 3 files)

- `structure Interaction.Oracle.Reduction` [ArkLib/Interaction/Oracle/Core.lean:1217](../../../ArkLib/Interaction/Oracle/Core.lean#L1217) — (no docstring)
- `structure Interaction.Reduction` [ArkLib/Interaction/Reduction.lean:187](../../../ArkLib/Interaction/Reduction.lean#L187) — (no docstring)
- `structure Reduction` [ArkLib/OracleReduction/Basic.lean:760](../../../ArkLib/OracleReduction/Basic.lean#L760) — An **interactive reduction** for a given protocol specification `pSpec`, and relative to oracles def

### `StraightlineExtractor` (3 declarations, 3 files)

- `abbrev Commitment.StraightlineExtractor` [ArkLib/CommitmentScheme/Basic.lean:178](../../../ArkLib/CommitmentScheme/Basic.lean#L178) — A **straightline extractor** for a commitment scheme takes in the commitment, the log of queries mad
- `def CommitmentScheme.StraightlineExtractor` [ArkLib/CommitmentScheme/CommitmentScheme.lean:123](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L123) — A **straightline extractor** for a standard commitment scheme takes the commitment and the log of qu
- `abbrev DuplexSpongeFS.NARG.StraightlineExtractor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:86](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L86) — Paper-facing alias for the straightline extractor interface used in Section 3.4.

### `Verifier` (3 declarations, 3 files)

- `structure Interaction.Oracle.Verifier` [ArkLib/Interaction/Oracle/Core.lean:1180](../../../ArkLib/Interaction/Oracle/Core.lean#L1180) — (no docstring)
- `abbrev Interaction.Verifier` [ArkLib/Interaction/Reduction.lean:130](../../../ArkLib/Interaction/Reduction.lean#L130) — (no docstring)
- `structure Verifier` [ArkLib/OracleReduction/Basic.lean:438](../../../ArkLib/OracleReduction/Basic.lean#L438) — A verifier of an interactive protocol is a function that takes in the input statement and the transc

### `absorb` (3 declarations, 3 files)

- `def DomainSeparator.absorb` [ArkLib/Data/Hash/DomainSep.lean:216](../../../ArkLib/Data/Hash/DomainSep.lean#L216) — Absorb `count` native elements. Rust interface: ```rust pub fn absorb(self, count: usize, label: &st
- `def DuplexSponge.absorb` [ArkLib/Data/Hash/DuplexSponge.lean:416](../../../ArkLib/Data/Hash/DuplexSponge.lean#L416) — ### Absorb a list of units into the sponge (paper version) Paper algorithm (process one element at a
- `def HashStateWithInstructions.absorb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:110](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L110) — Perform secure absorption of elements into the sponge. Rust interface: ```rust pub fn absorb(&mut se

### `antipodal_of_sum_zero` (3 declarations, 3 files)

- `theorem R12J.antipodal_of_sum_zero` [ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean:118](../../../ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean#L118) — **Antipodal tightness engine.** If the first `N` powers of `g` are `K`-linearly independent, any sub
- `theorem R12.antipodal_of_sum_zero` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean:95](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean#L95) — **General antipodal tightness.** If the first `N` powers of `ζ` are `K`-linearly independent (UNCOND
- `theorem R11.antipodal_of_sum_zero` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalQ.lean:91](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalQ.lean#L91) — **General unconditional antipodal tightness.** If the first `N` powers of `ζ` are `K`-linearly indep

### `antipode` (3 declarations, 3 files)

- `def Round23Rigidity.antipode` [ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean:43](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean#L43) — The antipode: `(j, ε) ↦ (j, ¬ε)` represents `∓ζ^j = −(±ζ^j)`.
- `def Round25General.antipode` [ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean:54](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean#L54) — The antipode `(j, ε) ↦ (j, ¬ε)`.
- `def Round24Triples.antipode` [ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean:48](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean#L48) — The antipode `(j, ε) ↦ (j, ¬ε)`.

### `badSet` (3 declarations, 3 files)

- `def Round17CAPair.badSet` [ArkLib/Data/CodingTheory/ProximityGap/CAPairExtractionEngine.lean:108](../../../ArkLib/Data/CodingTheory/ProximityGap/CAPairExtractionEngine.lean#L108) — `γ` is **`a`-bad** for `(f₁, f₂)` w.r.t. the code `C` if `f₁ + γ·f₂` agrees with some codeword on at
- `def LinePairCooccurrence.badSet` [ArkLib/Data/CodingTheory/ProximityGap/LinePairCooccurrenceBound.lean:85](../../../ArkLib/Data/CodingTheory/ProximityGap/LinePairCooccurrenceBound.lean#L85) — The bad set: line parameters whose point has agreement `≥ a` with both `c` and `c'`.
- `def ProximityGap.MCANearCapacity.badSet` [ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityLowerBound.lean:115](../../../ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityLowerBound.lean#L115) — The bad-scalar set `{ -(2j+1) : 0 ≤ j < n-1 }`.

### `binding` (3 declarations, 3 files)

- `def Commitment.binding` [ArkLib/CommitmentScheme/Basic.lean:170](../../../ArkLib/CommitmentScheme/Basic.lean#L170) — A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all adversar
- `def CommitmentScheme.binding` [ArkLib/CommitmentScheme/CommitmentScheme.lean:104](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L104) — A commitment scheme satisfies **binding** with error `bindingError` if every adversary's probability
- `theorem KZG.CommitmentScheme.binding` [ArkLib/CommitmentScheme/KZG/Binding.lean:737](../../../ArkLib/CommitmentScheme/KZG/Binding.lean#L737) — The KZG scheme satisfies evaluation binding provided `t`-SDH holds.

### `c0_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c0_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:95](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L95) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c0_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:113](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L113) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c0_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:130](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L130) — (no docstring)

### `c1_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c1_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:97](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L97) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c1_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:117](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L117) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c1_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:133](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L133) — (no docstring)

### `c2_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c2_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:101](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L101) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c2_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:121](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L121) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c2_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:136](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L136) — (no docstring)

### `c3_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c3_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:105](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L105) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c3_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:125](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L125) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c3_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:139](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L139) — (no docstring)

### `c4_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c4_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:109](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L109) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c4_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:129](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L129) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c4_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:142](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L142) — (no docstring)

### `c5_isRS` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.c5_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:113](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L113) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.c5_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:133](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L133) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c5_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:145](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L145) — (no docstring)

### `card_filter_eval_zero_le` (3 declarations, 3 files)

- `lemma ProximityGap.card_filter_eval_zero_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/AgreementCount.lean:45](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/AgreementCount.lean#L45) — Root-set cardinality bound (reproved inline to keep imports light): over a finite field a nonzero po
- `theorem RingSwitching.card_filter_eval_zero_le` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1858](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1858) — **Root-set cardinality bound.** Over an integral domain `L`, the number of field elements at which a
- `theorem Polynomial.card_filter_eval_zero_le` [ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean:57](../../../ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean#L57) — **Root-set cardinality bound.** Over a finite integral domain `L`, a nonzero `p : L[X]` vanishes at

### `cards` (3 declarations, 3 files)

- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257.cards` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat257.lean:64](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat257.lean#L64) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537.cards` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat65537.lean:54](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat65537.lean#L54) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyTowerF17.cards` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyTowerF17.lean:49](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyTowerF17.lean#L49) — (no docstring)

### `choose_le_add_add` (3 declarations, 3 files)

- `theorem Round14ConstantGap.choose_le_add_add` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarConstantGapBelowCapacity.lean:56](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarConstantGapBelowCapacity.lean#L56) — **The Pascal shift.** `C(n, m) ≤ C(n + j, m + j)` for every `j` (iterate the one-step).
- `theorem R15Bracket.choose_le_add_add` [ArkLib/Data/CodingTheory/ProximityGap/ScaleBracketFull.lean:283](../../../ArkLib/Data/CodingTheory/ProximityGap/ScaleBracketFull.lean#L283) — The Pascal shift: `C(n, m) ≤ C(n + j, m + j)`.
- `theorem Round18Bracket.choose_le_add_add` [ArkLib/Data/CodingTheory/ProximityGap/TwoSidedBracketScale.lean:205](../../../ArkLib/Data/CodingTheory/ProximityGap/TwoSidedBracketScale.lean#L205) — Pascal shift `C(n,m) ≤ C(n+j, m+j)`.

### `cliqueLocator` (3 declarations, 3 files)

- `def Round19Clique.cliqueLocator` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueBeachhead.lean:62](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueBeachhead.lean#L62) — The error locator of the clique support `E_α = W ∖ {α}`: `Λ_{E_α}(X) = ∏_{β ∈ W.erase α} (X − β)` —
- `def Round20CliqueKernel.cliqueLocator` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueKernelStructure.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueKernelStructure.lean#L60) — The clique error locator at vertex `α`: `Λ_{W∖{α}} = ∏_{β ∈ W.erase α} (X − β)`.
- `def Round21Relations.cliqueLocator` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueRelationModule.lean:56](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueRelationModule.lean#L56) — The clique error locator at vertex `α`: `Λ_{W∖{α}} = ∏_{β ∈ W.erase α} (X − β)`.

### `cliqueLocator_eval_other` (3 declarations, 3 files)

- `theorem Round19Clique.cliqueLocator_eval_other` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueBeachhead.lean:67](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueBeachhead.lean#L67) — **Diagonal evaluation, off-diagonal:** for `α' ∈ W`, `α' ≠ α`, the locator of `E_α` vanishes at `α'`
- `theorem Round20CliqueKernel.cliqueLocator_eval_other` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueKernelStructure.lean:105](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueKernelStructure.lean#L105) — Locator evaluation at the vertices: `Λ_{E_α}(β) = 0` for `β ∈ W`, `β ≠ α`.
- `theorem Round21Relations.cliqueLocator_eval_other` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueRelationModule.lean:78](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueRelationModule.lean#L78) — Locator evaluation off the diagonal vanishes.

### `cliqueLocator_eval_self_ne_zero` (3 declarations, 3 files)

- `theorem Round19Clique.cliqueLocator_eval_self_ne_zero` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueBeachhead.lean:84](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueBeachhead.lean#L84) — (no docstring)
- `theorem Round20CliqueKernel.cliqueLocator_eval_self_ne_zero` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueKernelStructure.lean:178](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueKernelStructure.lean#L178) — Locator self-evaluation is nonzero (distinct nodes).
- `theorem Round21Relations.cliqueLocator_eval_self_ne_zero` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueRelationModule.lean:86](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueRelationModule.lean#L86) — Locator self-evaluation is nonzero.

### `coeffVec` (3 declarations, 3 files)

- `def Round19Clique.coeffVec` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueBeachhead.lean:121](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueBeachhead.lean#L121) — The coefficient vector of a polynomial, truncated to `Fin N`.
- `def ArkLib.CodingTheory.Round7GeneralT.coeffVec` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorUnconditionalGeneralT.lean:188](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorUnconditionalGeneralT.lean#L188) — The **top-`t`-coefficient vector** of the monic root product `∏_{i∈S}(X − D i)` over the index windo
- `def CPoly.CMvPolynomial.degreeLE.coeffVec` [ArkLib/Data/MvPolynomial/ComputableDegreeLE.lean:111](../../../ArkLib/Data/MvPolynomial/ComputableDegreeLE.lean#L111) — Coefficient vector for a bounded-degree computable univariate polynomial.

### `coeff_pow_sub_at` (3 declarations, 3 files)

- `theorem ProximityPrize.HenselExistence.coeff_pow_sub_at` [ArkLib/Data/Polynomial/HenselExistence.lean:89](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L89) — Local copy of `NewtonLinearization.coeff_pow_sub_at` (order-`t` Newton linearization).
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_pow_sub_at` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:94](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L94) — **LEMMA B (Newton power linearization).** Local copy of `NewtonLinearization.coeff_pow_sub_at`.
- `theorem ProximityPrize.NewtonLinearization.coeff_pow_sub_at` [ArkLib/Data/Polynomial/NewtonLinearization.lean:98](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L98) — **Newton linearization at order `t`.** Under the below-`t` agreement hypothesis with `0 < t`, writin

### `coeff_pow_sub_below` (3 declarations, 3 files)

- `theorem ProximityPrize.HenselExistence.coeff_pow_sub_below` [ArkLib/Data/Polynomial/HenselExistence.lean:72](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L72) — Local copy of `NewtonLinearization.coeff_pow_sub_below` (truncation propagation).
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_pow_sub_below` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:76](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L76) — **LEMMA A (truncation propagation).** Agreement below order `t` propagates to every power. Local cop
- `theorem ProximityPrize.NewtonLinearization.coeff_pow_sub_below` [ArkLib/Data/Polynomial/NewtonLinearization.lean:62](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L62) — **Truncation propagation.** If `γ₁ γ₂ : R⟦X⟧` agree at every coefficient `j < t`, then so do `γ₁^i`

### `commit` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.Simple.commit` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:38](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L38) — Deterministically commit by multiplying the public matrix by the message vector.
- `def KZG.commit` [ArkLib/CommitmentScheme/KZG/Basic.lean:55](../../../ArkLib/CommitmentScheme/KZG/Basic.lean#L55) — To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of maximum deg
- `def SimpleRO.commit` [ArkLib/CommitmentScheme/SimpleRO.lean:43](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L43) — (no docstring)

### `commitmentScheme` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commitmentScheme` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:200](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L200) — The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound weak ver
- `def ArkLib.Lattices.Ajtai.Simple.commitmentScheme` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:56](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L56) — The simple Ajtai commitment as a `CommitmentScheme`. An opening is accepted only when the message sa
- `def SimpleRO.commitmentScheme` [ArkLib/CommitmentScheme/SimpleRO.lean:83](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L83) — (no docstring)

### `coreInteractionOracleReduction` (3 declarations, 3 files)

- `def coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1109](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1109) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1666](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1666) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1809](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1809) — Large-field reduction: Sumcheck seqCompose, then append FinalSum

### `coreInteractionOracleVerifier` (3 declarations, 3 files)

- `def coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1093](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1093) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1647](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1647) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1773](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1773) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum

### `coset_card` (3 declarations, 3 files)

- `theorem Code.coset_card` [ArkLib/Data/CodingTheory/Basic/CosetFarCount.lean:31](../../../ArkLib/Data/CodingTheory/Basic/CosetFarCount.lean#L31) — A coset `{w \| w - w₀ ∈ C}` of a linear code `C` has cardinality `\|C\|`.
- `theorem ArkLib.ProximityGap.CosetConcentration.coset_card` [ArkLib/Data/CodingTheory/ProximityGap/CosetPowerSumConcentration.lean:96](../../../ArkLib/Data/CodingTheory/ProximityGap/CosetPowerSumConcentration.lean#L96) — A coset of a primitive `h`-th root, with `g ≠ 0`, has exactly `h` elements.
- `theorem ArkLib.ProximityGap.HybridDepthNoGo.coset_card` [ArkLib/Data/CodingTheory/ProximityGap/HybridConcentrationDepthNoGo.lean:102](../../../ArkLib/Data/CodingTheory/ProximityGap/HybridConcentrationDepthNoGo.lean#L102) — (no docstring)

### `dom` (3 declarations, 3 files)

- `def ProximityGap.DeltaStarExactPin.dom` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean:79](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean#L79) — The smooth evaluation domain: `F₅* = ⟨2⟩` enumerated as successive powers of the generator `2`, i.e.
- `def ProximityGap.MCANearCapacityQuadratic.dom` [ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityQuadratic.lean:80](../../../ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityQuadratic.lean#L80) — The arithmetic evaluation domain `i ↦ (i : ZMod p)`, an embedding once `n ≤ p`.
- `def ArkLib.ProximityGap.RSPrizeDataPoint.dom` [ArkLib/Data/CodingTheory/ProximityGap/RSListSizeDataPoint.lean:42](../../../ArkLib/Data/CodingTheory/ProximityGap/RSListSizeDataPoint.lean#L42) — The smooth multiplicative domain mu_8 ⊂ (ZMod 17)ˣ : the eight 8th roots of unity, listed.

### `epsMCA_le_one` (3 declarations, 3 files)

- `theorem ProximityGap.MCAGS.epsMCA_le_one` [ArkLib/Data/CodingTheory/ProximityGap/141Math.lean:100](../../../ArkLib/Data/CodingTheory/ProximityGap/141Math.lean#L100) — **The abstract MCA error is a probability ceiling: `ε_mca ≤ 1`.** (Companion to `epsMCAgs_le_one`; t
- `theorem ProximityGap.epsMCA_le_one` [ArkLib/Data/CodingTheory/ProximityGap/Errors.lean:316](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean#L316) — The MCA error is bounded by the total probability mass.
- `theorem CodingTheory.Bridge.epsMCA_le_one` [ArkLib/ToMathlib/BridgeListDecodingCA.lean:77](../../../ArkLib/ToMathlib/BridgeListDecodingCA.lean#L77) — **`ε_mca ≤ 1`.** The mutual-correlated-agreement error is a supremum of PMF probabilities, hence at

### `evalCode` (3 declarations, 3 files)

- `def ProximityGap.CensusLowerBound.evalCode` [ArkLib/Data/CodingTheory/ProximityGap/CensusLowerBound.lean:61](../../../ArkLib/Data/CodingTheory/ProximityGap/CensusLowerBound.lean#L61) — Evaluations of polynomials of degree `< k` (i.e. `natDegree ≤ k − 1`) on a domain.
- `def ArkLib.ProximityGap.KKH26.evalCode` [ArkLib/Data/CodingTheory/ProximityGap/KKH26WitnessSpread.lean:74](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26WitnessSpread.lean#L74) — The explicit smooth-domain evaluation code: words on the `n`-point domain `{g^i : i < n}` that are e
- `def ArkLib.ProximityGap.TheoremQAssembly.evalCode` [ArkLib/Data/CodingTheory/ProximityGap/TheoremQAssembly.lean:54](../../../ArkLib/Data/CodingTheory/ProximityGap/TheoremQAssembly.lean#L54) — The evaluation code of polynomials of degree `< k` on the subtype domain of `H`.

### `evalDist_map_bijective_uniformSample` (3 declarations, 3 files)

- `theorem ArkLib.SeamChallengeRestriction.evalDist_map_bijective_uniformSample` [ArkLib/OracleReduction/Composition/Sequential/SeamChallengeRestriction.lean:49](../../../ArkLib/OracleReduction/Composition/Sequential/SeamChallengeRestriction.lean#L49) — **Uniform sampling pushed along a bijection.** For a bijection `f : α → β`, the pushforward of the u
- `theorem OptionTStateT.evalDist_map_bijective_uniformSample` [ArkLib/OracleReduction/RunUnroll.lean:384](../../../ArkLib/OracleReduction/RunUnroll.lean#L384) — **Uniform sampling pushed along a bijection.** Generalizes `evalDist_cast_uniformSample` from a type
- `lemma evalDist_map_bijective_uniformSample` [ArkLib/ToVCVio/UniformFamilyComap.lean:58](../../../ArkLib/ToVCVio/UniformFamilyComap.lean#L58) — **Pushing a uniform sample through a bijection is uniform.** `evalDist` form of `probOutput_map_bije

### `exp_quarter_primitive` (3 declarations, 3 files)

- `lemma DeBruijnIntRelations.exp_quarter_primitive` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntRelations.lean:847](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntRelations.lean#L847) — (no docstring)
- `lemma DeBruijnPrimePower.exp_quarter_primitive` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnPrimePower.lean:322](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnPrimePower.lean#L322) — (no docstring)
- `lemma WeightedPrimePowerPacket.exp_quarter_primitive` [ArkLib/Data/CodingTheory/ProximityGap/WeightedPrimePowerPacket.lean:376](../../../ArkLib/Data/CodingTheory/ProximityGap/WeightedPrimePowerPacket.lean#L376) — (no docstring)

### `exp_twelfth_primitive` (3 declarations, 3 files)

- `lemma DeBruijnTwoPrimeAssembly.exp_twelfth_primitive` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnTwoPrimeAssembly.lean:500](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnTwoPrimeAssembly.lean#L500) — (no docstring)
- `lemma DeBruijnWeightedCardTwoPrime.exp_twelfth_primitive` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedCardTwoPrime.lean:97](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedCardTwoPrime.lean#L97) — (no docstring)
- `lemma ThreadSplit.exp_twelfth_primitive` [ArkLib/Data/CodingTheory/ProximityGap/ThreadSplit.lean:297](../../../ArkLib/Data/CodingTheory/ProximityGap/ThreadSplit.lean#L297) — (no docstring)

### `finalSumcheckOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:127](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L127) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:668](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L668) — The oracle reduction for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1307](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1307) — The oracle reduction for the final sumcheck step

### `finalSumcheckOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:141](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L141) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1129](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1129) — Perfect completeness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1450](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1450) — **Final-sumcheck perfect completeness — proven.** The single-message final sumcheck reduction is per

### `finalSumcheckProver` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckProver` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:67](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L67) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:610](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L610) — The prover for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1210](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1210) — The prover for the final sumcheck step

### `finalSumcheckVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:101](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L101) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:644](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L644) — The verifier for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1246](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1246) — The verifier for the final sumcheck step

### `foldOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.foldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean:115](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean#L115) — (no docstring)
- `def Fri.Spec.FoldPhase.foldOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:534](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L534) — The oracle reduction that is the `i`-th round of the FRI protocol.
- `def WhirIOP.FoldRound.foldOracleReduction` [ArkLib/ProofSystem/Whir/FoldRound.lean:201](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L201) — The honest WHIR fold round as an oracle reduction.

### `fullOracleProof` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:98](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L98) — The full Binary Basefold protocol as a Proof
- `def Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:171](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L171) — The full Binary Basefold protocol as a Proof
- `def RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:111](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L111) — The full Binary Basefold protocol as a Proof

### `fullOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:70](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L70) — The reduction for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L140) — The reduction for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:99](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L99) — The reduction for the full Binary Basefold protocol

### `fullOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:113](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L113) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:191](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L191) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/General.lean:489](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L489) — **Issue #29: end-to-end RingSwitching perfect completeness (unconditional core).** The former five a

### `fullOracleVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:47](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L47) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:114](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L114) — The oracle verifier for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:63](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L63) — The oracle verifier for the full Binary Basefold protocol

### `fullOracleVerifier_rbrKnowledgeSoundness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:145](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L145) — Round-by-round knowledge soundness for the full Binary Basefold oracle verifier
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:237](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L237) — Round-by-round knowledge soundness for the full FRI-Binius oracle verifier.
- `theorem RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/General.lean:212](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L212) — Round-by-round knowledge soundness for the full ring-switching oracle verifier. `IsDomain K` (with t

### `fullRbrKnowledgeError` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:135](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L135) — Combined RBR knowledge soundness error for the full protocol
- `def Binius.FRIBinius.FullFRIBinius.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:227](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L227) — Combined RBR knowledge error for full FRI-Binius.
- `def RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/General.lean:196](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L196) — (no docstring)

### `hammingBall` (3 declarations, 3 files)

- `def ListDecodable.hammingBall` [ArkLib/Data/CodingTheory/ListDecodability.lean:27](../../../ArkLib/Data/CodingTheory/ListDecodability.lean#L27) — Hamming ball of radius `r` centred at a word `y`.
- `def Round13bSecondMoment.hammingBall` [ArkLib/Data/CodingTheory/ProximityGap/BallIntersectionSecondMomentLinear.lean:27](../../../ArkLib/Data/CodingTheory/ProximityGap/BallIntersectionSecondMomentLinear.lean#L27) — The Hamming ball of radius `r` around `c`.
- `def ArkLib.CodingTheory.Round13BallInter.hammingBall` [ArkLib/Data/CodingTheory/ProximityGap/ListAroundBallIntersectionKernel.lean:77](../../../ArkLib/Data/CodingTheory/ProximityGap/ListAroundBallIntersectionKernel.lean#L77) — The Hamming ball of radius `r` around `c`, as a finset of all words (the ambient `Fin n → F` is fini

### `honestTranscriptDist_reduction_evalDist` (3 declarations, 3 files)

- `theorem CheckClaim.honestTranscriptDist_reduction_evalDist` [ArkLib/ProofSystem/Component/CheckClaim.lean:121](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L121) — The honest transcript distribution for a valid `CheckClaim` statement is the deterministic empty tra
- `theorem ReduceClaim.honestTranscriptDist_reduction_evalDist` [ArkLib/ProofSystem/Component/ReduceClaim.lean:116](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L116) — The honest transcript distribution for `ReduceClaim` is the deterministic empty transcript. The mapp
- `theorem SendWitness.honestTranscriptDist_reduction_evalDist` [ArkLib/ProofSystem/Component/SendWitness.lean:109](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L109) — The honest transcript distribution for `SendWitness` is the deterministic one-message transcript con

### `hypotheses_satisfiable_zmod13` (3 declarations, 3 files)

- `theorem ArkLib.ProximityGap.Round8CompleteSquare.hypotheses_satisfiable_zmod13` [ArkLib/Data/CodingTheory/ProximityGap/MixedGaussSumCompleteSquare.lean:223](../../../ArkLib/Data/CodingTheory/ProximityGap/MixedGaussSumCompleteSquare.lean#L223) — **Non-vacuity (concrete odd-characteristic field with a primitive additive character).** `F = ZMod 1
- `theorem ArkLib.ProximityGap.Round8MixedGauss.hypotheses_satisfiable_zmod13` [ArkLib/Data/CodingTheory/ProximityGap/MixedGaussSumDiagonal.lean:221](../../../ArkLib/Data/CodingTheory/ProximityGap/MixedGaussSumDiagonal.lean#L221) — **Non-vacuity: a concrete odd-characteristic field with a primitive additive character.** `F = ZMod
- `theorem ArkLib.ProximityGap.Round7QuadraticGauss.hypotheses_satisfiable_zmod13` [ArkLib/Data/CodingTheory/ProximityGap/QuadraticGaussSumMagnitude.lean:279](../../../ArkLib/Data/CodingTheory/ProximityGap/QuadraticGaussSumMagnitude.lean#L279) — **Non-vacuity: a concrete odd-characteristic field with a primitive additive character.** `F = ZMod

### `isgn` (3 declarations, 3 files)

- `def Round23Rigidity.isgn` [ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean#L51) — The integer sign of a point.
- `def Round25General.isgn` [ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean:57](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean#L57) — The integer sign.
- `def Round24Triples.isgn` [ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean:56](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean#L56) — The integer sign.

### `knowledgeStateFunction` (3 declarations, 3 files)

- `def CheckClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/CheckClaim.lean:174](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L174) — The knowledge state function for the `CheckClaim` reduction. Since there is no challenge round, the
- `def RandomQuery.knowledgeStateFunction` [ArkLib/ProofSystem/Component/RandomQuery.lean:306](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L306) — The knowledge state function for the `RandomQuery` oracle reduction.
- `def ReduceClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:192](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L192) — The knowledge state function for the `ReduceClaim` reduction.

### `linearIndependent_pow_le` (3 declarations, 3 files)

- `theorem R12J.linearIndependent_pow_le` [ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean:93](../../../ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean#L93) — UNCONDITIONAL: over a field `K`, the first `N` powers of `ζ` are `K`-linearly independent whenever `
- `theorem R12.linearIndependent_pow_le` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean:62](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean#L62) — UNCONDITIONAL: over a field `K`, the first `N` powers of `ζ` are `K`-linearly independent whenever `
- `theorem R11.linearIndependent_pow_le` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalQ.lean:54](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalQ.lean#L54) — UNCONDITIONAL: over a field `K`, the first `N` powers of `ζ` are `K`-linearly independent whenever `

### `loc` (3 declarations, 3 files)

- `def C2CoreBound.loc` [ArkLib/Data/CodingTheory/ProximityGap/C2CoreEliminationBound.lean:62](../../../ArkLib/Data/CodingTheory/ProximityGap/C2CoreEliminationBound.lean#L62) — The error-locator polynomial of a support `E ⊆ F`.
- `def NormalRank.loc` [ArkLib/Data/CodingTheory/ProximityGap/NormalRankSharpThreshold.lean:52](../../../ArkLib/Data/CodingTheory/ProximityGap/NormalRankSharpThreshold.lean#L52) — The error-locator polynomial of a support `E ⊆ F` (also in `C2CoreBound.loc`; duplicated here to kee
- `def TopLine.loc` [ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean:55](../../../ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean#L55) — The error-locator polynomial of a support.

### `natDegree_eval_le` (3 declarations, 3 files)

- `theorem ArkLib.ProximityGap.Issue232Bricks.natDegree_eval_le` [ArkLib/Data/CodingTheory/ProximityGap/VerifiedBricks.lean:313](../../../ArkLib/Data/CodingTheory/ProximityGap/VerifiedBricks.lean#L313) — **GS degree budget.** For `H ∈ F[X][Y]` whose `Y`-coefficients all have `X`-degree `≤ B` (`B = deg_X
- `theorem ArkLib.IncidenceBound.natDegree_eval_le` [ArkLib/ToMathlib/IncidenceBound.lean:111](../../../ArkLib/ToMathlib/IncidenceBound.lean#L111) — Degree accounting for the incidence polynomial: `natDegree (B.eval v) ≤ degreeX B + natDegree_Y B ·
- `theorem ArkLib.XiCertReduction.natDegree_eval_le` [ArkLib/ToMathlib/XiCertReduction.lean:228](../../../ArkLib/ToMathlib/XiCertReduction.lean#L228) — **The composition degree bound**: substituting `v : F[X]` for the `Y` variable of a bivariate `p` gi

### `nodal` (3 declarations, 3 files)

- `def Round21Relations.nodal` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueRelationModule.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueRelationModule.lean#L60) — The nodal polynomial `Λ_W = ∏_{β ∈ W} (X − β)`.
- `def Round27Core.nodal` [ArkLib/Data/CodingTheory/ProximityGap/RigiditySunflowerCore.lean:46](../../../ArkLib/Data/CodingTheory/ProximityGap/RigiditySunflowerCore.lean#L46) — The nodal polynomial of a finset.
- `def UniPoly.Lagrange.nodal` [ArkLib/Data/UniPoly/Basic.lean:1112](../../../ArkLib/Data/UniPoly/Basic.lean#L1112) — (no docstring)

### `oracleReduction_completeness` (3 declarations, 3 files)

- `theorem RandomQuery.oracleReduction_completeness` [ArkLib/ProofSystem/Component/RandomQuery.lean:130](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L130) — The `RandomQuery` oracle reduction is perfectly complete.
- `theorem ReduceClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:293](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L293) — The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. Proof strategy m
- `theorem SendSingleWitness.oracleReduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:514](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L514) — The `SendSingleWitness` oracle reduction satisfies perfect completeness.

### `p0_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p0_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:118](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L118) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p0_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:142](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L142) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p0_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:152](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L152) — (no docstring)

### `p1_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p1_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:119](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L119) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p1_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:143](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L143) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p1_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:153](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L153) — (no docstring)

### `p2_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p2_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:120](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L120) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p2_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:144](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L144) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p2_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:154](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L154) — (no docstring)

### `p3_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p3_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:121](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L121) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p3_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:145](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L145) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p3_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:155](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L155) — (no docstring)

### `p4_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p4_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:122](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L122) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p4_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:146](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L146) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p4_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:156](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L156) — (no docstring)

### `p5_deg` (3 declarations, 3 files)

- `lemma ArkLib.CodingTheory.TinyInteriorPin.p5_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:123](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L123) — (no docstring)
- `lemma ArkLib.CodingTheory.TinyInteriorK3.p5_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:147](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L147) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p5_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:157](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L157) — (no docstring)

### `phi` (3 declarations, 3 files)

- `def CodingTheory.Bounds.phi` [ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean:48](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean#L48) — Explicit `F`-algebra retraction of `psi`, sending `Y ↦ X₁` and coefficients `g(X) ↦ g(X₀)`.
- `def ArkLib.CodingTheory.JohnsonSimplex.phi` [ArkLib/Data/CodingTheory/ProximityGap/JohnsonSimplexBound.lean:42](../../../ArkLib/Data/CodingTheory/ProximityGap/JohnsonSimplexBound.lean#L42) — The q-ary simplex embedding: `φ(x)(i,c) = 1` if `x i = c`, else `0`.
- `def Logup.phi` [ArkLib/ProofSystem/Logup/Common.lean:685](../../../ArkLib/ProofSystem/Logup/Common.lean#L685) — The denominator term `φᵢ(u)` from Protocol 2.

### `pow_mod_eq` (3 declarations, 3 files)

- `lemma CRTExponentGridSum.pow_mod_eq` [ArkLib/Data/CodingTheory/ProximityGap/CRTExponentGridSum.lean:71](../../../ArkLib/Data/CodingTheory/ProximityGap/CRTExponentGridSum.lean#L71) — Exponent reduction: if `ζ ^ n = 1` then `ζ ^ (m % n) = ζ ^ m`.
- `lemma DeBruijnWeightedSquarefreeExp.pow_mod_eq` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedSquarefreeExp.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedSquarefreeExp.lean#L51) — `ζ` absorbs reduction of exponents mod `n`.
- `lemma LamLeungMultisetAntipodal.pow_mod_eq` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungMultisetAntipodal.lean:47](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungMultisetAntipodal.lean#L47) — Powers of an `n`-torsion element only see exponents mod `n`.

### `reduction_isHVZK` (3 declarations, 3 files)

- `theorem CheckClaim.reduction_isHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:156](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L156) — `CheckClaim` has an explicit perfect-HVZK simulator.
- `theorem DoNothing.reduction_isHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:79](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L79) — The `DoNothing` reduction has an explicit perfect-HVZK simulator for any relation.
- `theorem ReduceClaim.reduction_isHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:153](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L153) — `ReduceClaim` has an explicit perfect-HVZK simulator for any input relation.

### `reduction_isStatHVZK` (3 declarations, 3 files)

- `theorem CheckClaim.reduction_isStatHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:161](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L161) — `CheckClaim` has statistical HVZK at every error budget.
- `theorem DoNothing.reduction_isStatHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:85](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L85) — The `DoNothing` reduction has statistical HVZK for any relation and error budget.
- `theorem ReduceClaim.reduction_isStatHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:159](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L159) — `ReduceClaim` has statistical HVZK for any input relation and error budget.

### `reduction_perfectHVZK` (3 declarations, 3 files)

- `theorem CheckClaim.reduction_perfectHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:142](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L142) — `CheckClaim` is perfectly HVZK for the predicate relation. The simulator is the identity transcript
- `theorem DoNothing.reduction_perfectHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:64](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L64) — The `DoNothing` reduction is perfectly HVZK for any relation.
- `theorem ReduceClaim.reduction_perfectHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:138](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L138) — `ReduceClaim` is perfectly HVZK for any input relation: it has no messages or challenges, so the ide

### `reduction_statisticalHVZK` (3 declarations, 3 files)

- `theorem CheckClaim.reduction_statisticalHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:150](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L150) — Perfect HVZK implies statistical HVZK at every error budget.
- `theorem DoNothing.reduction_statisticalHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:71](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L71) — The `DoNothing` reduction is statistically HVZK for any relation and error budget.
- `theorem ReduceClaim.reduction_statisticalHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:146](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L146) — Perfect HVZK implies statistical HVZK for `ReduceClaim` at every error budget.

### `relOut` (3 declarations, 3 files)

- `def CheckClaim.relOut` [ArkLib/ProofSystem/Component/CheckClaim.lean:64](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L64) — (no docstring)
- `def RandomQuery.relOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:52](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L52) — The output relation states that if the verifier's single query was `q`, then `a` and `b` agree on th
- `def SendClaim.relOut` [ArkLib/ProofSystem/Component/SendClaim.lean:102](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L102) — (no docstring)

### `rename_finCongr_heq` (3 declarations, 3 files)

- `lemma RingSwitching.SumcheckPhase.rename_finCongr_heq` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:317](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L317) — Renaming a polynomial along the canonical index `finCongr` of a (propositional) dimension equality `
- `lemma Sumcheck.Structured.rename_finCongr_heq` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:140](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L140) — Renaming a polynomial along the canonical index `finCongr` of a dimension equality is heterogeneousl
- `theorem MvPolynomial.rename_finCongr_heq` [ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean:46](../../../ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean#L46) — Renaming along the canonical `finCongr` of a dimension equality is heterogeneously equal to the orig

### `root` (3 declarations, 3 files)

- `def R12J.root` [ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean:107](../../../ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean#L107) — Value of the root indexed by `(j,b)` under the antipodal pairing: `root g (j,false) = g^j`, `root g
- `def R12.root` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean:80](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean#L80) — The value of the root indexed by `(j,b)`: `root(j,false) = ζ^j`, `root(j,true) = -ζ^j`.
- `def R11.root` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalQ.lean:77](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalQ.lean#L77) — The complex value of the root indexed by `(j,b)` under the antipodal pairing `root(j,false) = ζ^j`,

### `root_true_eq` (3 declarations, 3 files)

- `theorem R12J.root_true_eq` [ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean:111](../../../ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean#L111) — The `(j,true)` root is the genuine `(j+N)`-th power of `g` when `g^N=-1`.
- `theorem R12.root_true_eq` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean:86](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean#L86) — For a 2N-th root of unity with `ζ^N = -1`, the `(j,true)` root is the genuine `(j+N)`-th power of `ζ
- `theorem R11.root_true_eq` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalQ.lean:82](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalQ.lean#L82) — For a 2N-th root of unity with `ζ^N = -1`, the `(j,true)` root really is the `(j+N)`-th genuine powe

### `seqComposeError_eq_append` (3 declarations, 3 files)

- `theorem Verifier.seqComposeError_eq_append` [ArkLib/OracleReduction/Composition/Sequential/General.lean:608](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L608) — The RBR error of a sequential composition, expressed via `seqComposeChallengeIdxToSigma` over the *g
- `theorem ArkLib.SeqComposeRbrKnowledge.seqComposeError_eq_append` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:130](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L130) — **The composed RBR error, indexed via `seqComposeChallengeIdxToSigma` over the global challenge inde
- `theorem ArkLib.SeqComposeRbrSoundness.seqComposeError_eq_append` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:152](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L152) — **The composed RBR error, indexed via `seqComposeChallengeIdxToSigma` over the global challenge inde

### `simulateQ_simOracle2_messageQuery` (3 declarations, 3 files)

- `lemma RingSwitching.BatchingPhase.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:71](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L71) — Local message-query collapse for `OracleInterface.simOracle2`.
- `lemma RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1521](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1521) — **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
- `lemma ToyProblem.Spec.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:718](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L718) — `simOracle2` message-query collapse (`OracleComp` form), RIGHT (message) family.

### `squeeze` (3 declarations, 3 files)

- `def DomainSeparator.squeeze` [ArkLib/Data/Hash/DomainSep.lean:241](../../../ArkLib/Data/Hash/DomainSep.lean#L241) — Squeeze `count` native elements. Rust interface: ```rust pub fn squeeze(self, count: usize, label: &
- `def DuplexSponge.squeeze` [ArkLib/Data/Hash/DuplexSponge.lean:512](../../../ArkLib/Data/Hash/DuplexSponge.lean#L512) — ### Squeeze out a vector of units from the sponge (paper version) We differ from the paper version i
- `def HashStateWithInstructions.squeeze` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:149](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L149) — Perform a secure squeeze operation. Rust interface: ```rust pub fn squeeze(&mut self, output: &mut [

### `subsetSumCount` (3 declarations, 3 files)

- `def ArkLib.ProximityGap.Round4CharacterSum.subsetSumCount` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumCharacterSum.lean:94](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumCharacterSum.lean#L94) — The subgroup subset-sum count `N(m, target) = #{ S ⊆ G : \|S\| = m, ∑_{x∈S} x = target }`, as a `Finse
- `def ArkLib.ProximityGap.Round4PairingRecursion.subsetSumCount` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPairingInflate.lean:238](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPairingInflate.lean#L238) — **The subset-sum count.** `N(g, c, target)` is the number of subsets `S ⊆ G` (modelled as `Finset (F
- `def ArkLib.ProximityGap.Round4NewtonVietaUpper.subsetSumCount` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPigeonholeFiber.lean:88](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPigeonholeFiber.lean#L88) — The §7 **subgroup subset-sum fiber count** `N(a, target)`: the number of size-`a` subsets of the gro

### `sum_char_eq_ite` (3 declarations, 3 files)

- `theorem ArkLib.ProximityGap.MomentCollisionSpectral.sum_char_eq_ite` [ArkLib/Data/CodingTheory/ProximityGap/MomentCollisionSpectral.lean:70](../../../ArkLib/Data/CodingTheory/ProximityGap/MomentCollisionSpectral.lean#L70) — Second orthogonality relation, restated: `∑_{ψ} ψ y = \|A\| · [y = 0]`.
- `theorem ArkLib.ProximityGap.Round9SubgroupCharExpansion.sum_char_eq_ite` [ArkLib/Data/CodingTheory/ProximityGap/Round9SubgroupCharExpansion.lean:80](../../../ArkLib/Data/CodingTheory/ProximityGap/Round9SubgroupCharExpansion.lean#L80) — **Second orthogonality, full form.** `∑_{χ} χ(a) = \|M\|` if `a = 1`, else `0`.
- `lemma ArkLib.CodingTheory.CharacterSum.sum_char_eq_ite` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupCharacterSumNoGo.lean:97](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupCharacterSumNoGo.lean#L97) — **Per-coordinate character orthogonality.** For each `i`, the sum over additive characters of `F` of

### `sval` (3 declarations, 3 files)

- `def Round23Rigidity.sval` [ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean:38](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean#L38) — A signed half-basis point `(j, ε)` represents the `2N`-th root `±ζ^j`.
- `def Round25General.sval` [ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean:50](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean#L50) — A signed half-basis point `(j, ε)` represents the `2N`-th root `±ζ^j`.
- `def Round24Triples.sval` [ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean:44](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean#L44) — A signed half-basis point `(j, ε)` represents the `2N`-th root `±ζ^j`.

### `sval_antipode` (3 declarations, 3 files)

- `theorem Round23Rigidity.sval_antipode` [ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean:46](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean#L46) — (no docstring)
- `theorem Round29IteratedLift.sval_antipode` [ArkLib/Data/CodingTheory/ProximityGap/RigidityIterated2kLift.lean:296](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityIterated2kLift.lean#L296) — The antipode flips the sign of `sval`.
- `theorem Round24Triples.sval_antipode` [ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean#L51) — (no docstring)

### `sval_eq_sum` (3 declarations, 3 files)

- `theorem Round23Rigidity.sval_eq_sum` [ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean#L60) — Each `sval` is the basis expansion of its (single-index, signed) coefficient.
- `theorem Round25General.sval_eq_sum` [ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean:88](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean#L88) — (no docstring)
- `theorem Round24Triples.sval_eq_sum` [ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean#L63) — Each `sval` expands over the half basis with its integer coefficient profile.

### `toVerifier` (3 declarations, 3 files)

- `def Interaction.OracleDecoration.OracleReduction.toVerifier` [ArkLib/Interaction/Oracle/Core.lean:1096](../../../ArkLib/Interaction/Oracle/Core.lean#L1096) — (no docstring)
- `def Interaction.PublicCoinVerifier.toVerifier` [ArkLib/Interaction/Reduction.lean:162](../../../ArkLib/Interaction/Reduction.lean#L162) — (no docstring)
- `def OracleVerifier.toVerifier` [ArkLib/OracleReduction/Basic.lean:553](../../../ArkLib/OracleReduction/Basic.lean#L553) — An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface using it

### `totient_two_pow` (3 declarations, 3 files)

- `lemma ArkLib.ProximityGap.KKH26.totient_two_pow` [ArkLib/Data/CodingTheory/ProximityGap/KKH26SumsOfRootsOfUnity.lean:135](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26SumsOfRootsOfUnity.lean#L135) — (no docstring)
- `theorem R12.totient_two_pow` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean:140](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean#L140) — `φ(2^m) = 2^{m-1}` for `m ≥ 1`.
- `theorem ArkLib.ProximityGap.SubsetSumLowerLoop50.totient_two_pow` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumLowerLoop50.lean:183](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumLowerLoop50.lean#L183) — `φ(2^m) = 2^{m-1}` for `m ≥ 1`.

### `transcriptSimulator` (3 declarations, 3 files)

- `def RandomQuery.transcriptSimulator` [ArkLib/ProofSystem/Component/RandomQuery.lean:203](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L203) — The simulator for `RandomQuery`: the protocol is witness-free, so the simulator can rerun the honest
- `def SendClaim.transcriptSimulator` [ArkLib/ProofSystem/Component/SendClaim.lean:246](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L246) — The simulator for `SendClaim`: the component has no private witness, so the simulator can run the ho
- `def SendWitness.transcriptSimulator` [ArkLib/ProofSystem/Component/SendWitness.lean:103](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L103) — The simulator for the `SendWitness` reduction when the relation's witness is determined by the input

### `ubad` (3 declarations, 3 files)

- `def ProximityGap.DeltaStarExactPin.ubad` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean:145](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean#L145) — The bad stack as a `WordStack`.
- `def CodingTheory.LineDecodingRefutation.ubad` [ArkLib/Data/CodingTheory/ProximityGap/LineDecodingRefutation.lean:113](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecodingRefutation.lean#L113) — The refuting stack: `u 0 = 0`, `u 1 = 1` (the all-ones word of `Fin 1 → ZMod 2`).
- `def ProximityGap.MCAZeroCode.ubad` [ArkLib/Data/CodingTheory/ProximityGap/MCAZeroCodeExact.lean:57](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAZeroCodeExact.lean#L57) — The refuting/witness stack: `u 0 = 0`, `u 1 = 𝟙` (the all-ones word `ι → F`).

### `ubad_one` (3 declarations, 3 files)

- `theorem ProximityGap.DeltaStarExactPin.ubad_one` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean:149](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean#L149) — (no docstring)
- `theorem CodingTheory.LineDecodingRefutation.ubad_one` [ArkLib/Data/CodingTheory/ProximityGap/LineDecodingRefutation.lean:118](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecodingRefutation.lean#L118) — (no docstring)
- `theorem ProximityGap.MCAZeroCode.ubad_one` [ArkLib/Data/CodingTheory/ProximityGap/MCAZeroCodeExact.lean:61](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAZeroCodeExact.lean#L61) — (no docstring)

### `ubad_zero` (3 declarations, 3 files)

- `theorem ProximityGap.DeltaStarExactPin.ubad_zero` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean:147](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean#L147) — (no docstring)
- `theorem CodingTheory.LineDecodingRefutation.ubad_zero` [ArkLib/Data/CodingTheory/ProximityGap/LineDecodingRefutation.lean:115](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecodingRefutation.lean#L115) — (no docstring)
- `theorem ProximityGap.MCAZeroCode.ubad_zero` [ArkLib/Data/CodingTheory/ProximityGap/MCAZeroCodeExact.lean:59](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAZeroCodeExact.lean#L59) — (no docstring)

### `verify` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.Simple.verify` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:46](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L46) — Verify a simple Ajtai opening by checking the matrix product.
- `def SimpleRO.verify` [ArkLib/CommitmentScheme/SimpleRO.lean:50](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L50) — (no docstring)
- `def OracleVerifier.Append.verify` [ArkLib/OracleReduction/Composition/Sequential/Append.lean:377](../../../ArkLib/OracleReduction/Composition/Sequential/Append.lean#L377) — The composite `verify`: run `V₁` (routed by `router₁`) to obtain the intermediate statement, then ru

### `window_step` (3 declarations, 3 files)

- `lemma DeBruijnIntWindowedLaw.window_step` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntWindowedLaw.lean:131](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntWindowedLaw.lean#L131) — **One upgrade step**: a window-`t` combination plus the `(t+1)`-st power sum upgrades to a window-`(
- `lemma DeBruijnWeightedWindowLaw.window_step` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedWindowLaw.lean:164](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedWindowLaw.lean#L164) — **One upgrade step**: a window-`t` combination plus the `(t+1)`-st power sum upgrades to a window-`(
- `lemma DeBruijnWindowedLaw.window_step` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWindowedLaw.lean:232](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWindowedLaw.lean#L232) — **One upgrade step**: a `t`-window decomposition plus the `(t+1)`-st power sum upgrades to a `(t+1)`

### `zeta` (3 declarations, 3 files)

- `def R12J.General.zeta` [ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean:168](../../../ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean#L168) — The primitive `2^m`-th root of unity we work with.
- `def Concrete.zeta` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean:209](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean#L209) — The explicit primitive `2^m`-th root of unity `exp(2πi/2^m)` in `ℂ`.
- `def ArkLib.ProximityGap.SubgroupQuadraticSecondMoment.zeta` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupQuadraticSecondMoment.lean:54](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupQuadraticSecondMoment.lean#L54) — The quadratic subgroup Gauss sum at frequency `b`: `ζ_b = ∑_{x∈G} ψ(b·x²)`.

### `card_le_natDegreeY_of_sub_C_dvd` (3 declarations, 3 files)

- `theorem R14.card_le_natDegreeY_of_sub_C_dvd` [ArkLib/Data/CodingTheory/ProximityGap/GSYDegreeListCap.lean:45](../../../ArkLib/Data/CodingTheory/ProximityGap/GSYDegreeListCap.lean#L45) — **Y-degree list cap.**  If `Q ≠ 0` in `(F[X])[Y]` and every `f` in the finite set `S ⊆ F[X]` gives a
- `theorem R15.card_le_natDegreeY_of_sub_C_dvd` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:259](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L259) — **Y-degree list cap.** If `Q ≠ 0` in `(F[X])[Y]` and every `f ∈ S` gives a linear factor `Y - C f` o
- `theorem R15.card_le_natDegreeY_of_sub_C_dvd` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:259](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L259) — **Y-degree list cap.** If `Q ≠ 0` in `(F[X])[Y]` and every `f ∈ S` gives a linear factor `Y - C f` o

### `coeffPoly_evalEval` (3 declarations, 3 files)

- `lemma GSInterp.coeffPoly_evalEval` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:119](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L119) — (no docstring)
- `lemma R15.coeffPoly_evalEval` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:126](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L126) — (no docstring)
- `lemma R15.coeffPoly_evalEval` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:126](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L126) — (no docstring)

### `evalAtPoints` (3 declarations, 3 files)

- `def GSInterp.evalAtPoints` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:133](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L133) — The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
- `def R15.evalAtPoints` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:140](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L140) — The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
- `def R15.evalAtPoints` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:140](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L140) — The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria

### `evalAtPoints_apply` (3 declarations, 3 files)

- `lemma GSInterp.evalAtPoints_apply` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:143](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L143) — (no docstring)
- `lemma R15.evalAtPoints_apply` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:150](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L150) — (no docstring)
- `lemma R15.evalAtPoints_apply` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:150](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L150) — (no docstring)

### `factor_of_agreement` (3 declarations, 3 files)

- `theorem GSRootOrder.factor_of_agreement` [ArkLib/Data/CodingTheory/ProximityGap/GSRootOrderStep.lean:52](../../../ArkLib/Data/CodingTheory/ProximityGap/GSRootOrderStep.lean#L52) — **The root-order / factor step (Sudan, multiplicity 1).**  Let `Q : (F[X])[Y]` satisfy the `(1, k−1)
- `theorem R15.factor_of_agreement` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:233](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L233) — **Root-order / factor step (multiplicity 1).** `≥ D` vanishing points of the degree-`< D` univariate
- `theorem R15.factor_of_agreement` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:233](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L233) — **Root-order / factor step (multiplicity 1).** `≥ D` vanishing points of the degree-`< D` univariate

### `pins` (3 declarations, 3 files)

- `theorem ClassChart.pins` [ArkLib/Data/CodingTheory/ProximityGap/ClassChartBounds.lean:246](../../../ArkLib/Data/CodingTheory/ProximityGap/ClassChartBounds.lean#L246) — (no docstring)
- `structure pins` [ArkLib/Data/CodingTheory/ProximityGap/JointT2FiberTightness.lean:42](../../../ArkLib/Data/CodingTheory/ProximityGap/JointT2FiberTightness.lean#L42) — (no docstring)
- `structure pins` [ArkLib/Data/CodingTheory/ProximityGap/ListRecoveryInterleavedGap.lean:18](../../../ArkLib/Data/CodingTheory/ProximityGap/ListRecoveryInterleavedGap.lean#L18) — (no docstring)

### `qIdx` (3 declarations, 3 files)

- `def GSExactWall.qIdx` [ArkLib/Data/CodingTheory/ProximityGap/GSExactCountWall.lean:26](../../../ArkLib/Data/CodingTheory/ProximityGap/GSExactCountWall.lean#L26) — The number of genuinely contributing indices: `q = ⌈D/c⌉ = (D + c − 1)/c`.
- `abbrev DuplexSpongeFS.Sponge314.K1.qIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L69) — The oracle index of the single adversary query: `p⁻¹(s₀)`.
- `abbrev DuplexSpongeFS.Sponge314.K1.qIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L69) — The oracle index of the single adversary query: `p⁻¹(s₀)`.

### `sudan_interpolation_exists` (3 declarations, 3 files)

- `theorem GSInterp.sudan_interpolation_exists` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:150](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L150) — (no docstring)
- `theorem R15.sudan_interpolation_exists` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:156](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L156) — **Sudan (multiplicity-1) interpolation existence.**
- `theorem R15.sudan_interpolation_exists` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:156](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L156) — **Sudan (multiplicity-1) interpolation existence.**

### `support` (3 declarations, 3 files)

- `def support` [ArkLib/Data/CodingTheory/ProximityGap/PromotedHypothesesB.lean:68](../../../ArkLib/Data/CodingTheory/ProximityGap/PromotedHypothesesB.lean#L68) — (no docstring)
- `def ArkLib.ProximityGap.Round5SecondMoment.support` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPigeonholeManyTargets.lean:146](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPigeonholeManyTargets.lean#L146) — The **support**: the set of targets actually hit by some size-`a` subset sum, `{ target : N(a, targe
- `def support` [ArkLib/Data/CodingTheory/Quarantine/Hypotheses.lean:20](../../../ArkLib/Data/CodingTheory/Quarantine/Hypotheses.lean#L20) — (no docstring)

### `uniform_event_mass` (3 declarations, 3 files)

- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:55](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L55) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly
- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:166](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L166) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly
- `theorem uniform_event_mass` [ArkLib/ToMathlib/CountingAgreementBricks.lean:109](../../../ArkLib/ToMathlib/CountingAgreementBricks.lean#L109) — The mass of a finite event under the uniform distribution is its cardinality divided by the sample-s

### `audit` (3 declarations, 3 files)

- `axiom audit` [ArkLib/ProofSystem/Logup/Security/LogupCompletenessUncond.lean:84](../../../ArkLib/ProofSystem/Logup/Security/LogupCompletenessUncond.lean#L84) — (no docstring)
- `axiom audit` [ArkLib/ProofSystem/Logup/Security/LogupProtocol2Status.lean:95](../../../ArkLib/ProofSystem/Logup/Security/LogupProtocol2Status.lean#L95) — (no docstring)
- `axiom audit` [ArkLib/ProofSystem/Logup/Security/LogupSoundnessUncond.lean:84](../../../ArkLib/ProofSystem/Logup/Security/LogupSoundnessUncond.lean#L84) — (no docstring)

### `composedPSpec_dir_seam` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.composedPSpec_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:428](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L428) — Seam-direction fact for `firstMessage ▷ sfx1`: the combined spec (= `composedPSpec`) at the seam ind
- `theorem Spartan.Spec.Bricks.composedPSpec_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:223](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L223) — Seam-direction fact for `firstMessage ▷ sfx1`: the combined spec (= `composedPSpec`) at the seam ind
- `theorem Spartan.Spec.Bricks.composedPSpec_dir_seam` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:171](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L171) — Seam-direction fact for `firstMessage ▷ sfx1`: the combined spec (= `composedPSpec`) at the seam ind

### `prizeRate_floor_add_one_le` (3 declarations, 3 files)

- `lemma ProximityGap.prizeRate_floor_add_one_le` [ArkLib/Data/CodingTheory/ProximityGap/Decision.lean:149](../../../ArkLib/Data/CodingTheory/ProximityGap/Decision.lean#L149) — For `n ≥ 2`, every prize-rate degree satisfies `k_j + 1 ≤ n`.
- `lemma ProximityGap.prizeRate_floor_add_one_le` [ArkLib/Data/CodingTheory/ProximityGap/LDFourRate.lean:218](../../../ArkLib/Data/CodingTheory/ProximityGap/LDFourRate.lean#L218) — If the evaluation domain has at least two points, each prize degree is strictly below the block leng
- `lemma ProximityGap.prizeRate_floor_add_one_le` [ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean:371](../../../ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean#L371) — For `n ≥ 2`, every prize-rate degree satisfies `k_j + 1 ≤ n`.

### `secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` [ArkLib/ProofSystem/Spartan/TightComposedComplete.lean:278](../../../ArkLib/ProofSystem/Spartan/TightComposedComplete.lean#L278) — **Leaf `h₇` (tight chain): the binding strengthening of the carried second sum-check completeness.**
- `theorem Spartan.Spec.Bricks.secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:264](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L264) — **The binding strengthening of the carried second sum-check completeness** (#329, B7): the enriched
- `theorem Spartan.Spec.Bricks.secondSumcheckWithTarget_perfectCompleteness_enrichedBinding` [ArkLib/ProofSystem/Spartan/TightSecondBinding.lean:47](../../../ArkLib/ProofSystem/Spartan/TightSecondBinding.lean#L47) — **The binding strengthening of the carried second sum-check completeness** (#329, B7): the enriched

### `sfx1_dir_seam` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx1_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:412](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L412) — Seam-direction fact for `firstChallenge ▷ sfx2`: the combined spec (= `sfx1`) at the seam index `1`
- `theorem Spartan.Spec.Bricks.sfx1_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:207](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L207) — Seam-direction fact for `firstChallenge ▷ sfx2`: the combined spec (= `sfx1`) at the seam index `1`
- `theorem Spartan.Spec.Bricks.sfx1_dir_seam` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:155](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L155) — Seam-direction fact for `firstChallenge ▷ sfx2`: the combined spec (= `sfx1`) at the seam index `1`

### `sfx1_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx1_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:400](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L400) — `sfx1 = ⟨V_to_P, FirstChallenge⟩ ++ₚ sfx2` opens `V_to_P`.
- `theorem Spartan.Spec.Bricks.sfx1_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:195](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L195) — `sfx1 = ⟨V_to_P, FirstChallenge⟩ ++ₚ sfx2` opens `V_to_P`.
- `theorem Spartan.Spec.Bricks.sfx1_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:143](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L143) — `sfx1 = ⟨V_to_P, FirstChallenge⟩ ++ₚ sfx2` opens `V_to_P`.

### `sfx2_dir_seam` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx2_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:386](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L386) — Seam-direction fact for `firstSumcheck ▷ sfx3`: the combined spec (= `sfx2`) at the seam index `vsum
- `theorem Spartan.Spec.Bricks.sfx2_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:181](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L181) — Seam-direction fact for `firstSumcheck ▷ sfx3`: the combined spec (= `sfx2`) at the seam index `vsum
- `theorem Spartan.Spec.Bricks.sfx2_dir_seam` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:129](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L129) — Seam-direction fact for `firstSumcheck ▷ sfx3`: the combined spec (= `sfx2`) at the seam index `vsum

### `sfx2_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx2_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:372](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L372) — `sfx2 = sumcheck₃ ++ₚ sfx3` opens `P_to_V` (first sum-check's leading message).
- `theorem Spartan.Spec.Bricks.sfx2_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:167](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L167) — `sfx2 = sumcheck₃ ++ₚ sfx3` opens `P_to_V` (first sum-check's leading message).
- `theorem Spartan.Spec.Bricks.sfx2_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:115](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L115) — `sfx2 = sumcheck₃ ++ₚ sfx3` opens `P_to_V` (first sum-check's leading message).

### `sfx3_dir_seam` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx3_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:361](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L361) — Seam-direction fact for `sendEvalClaim ▷ sfx4`: the combined spec (= `sfx3`) at the seam index `1` i
- `theorem Spartan.Spec.Bricks.sfx3_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:156](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L156) — Seam-direction fact for `sendEvalClaim ▷ sfx4`: the combined spec (= `sfx3`) at the seam index `1` i
- `theorem Spartan.Spec.Bricks.sfx3_dir_seam` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:104](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L104) — Seam-direction fact for `sendEvalClaim ▷ sfx4`: the combined spec (= `sfx3`) at the seam index `1` i

### `sfx3_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx3_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:351](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L351) — `sfx3 = ⟨P_to_V, EvalClaim⟩ ++ₚ sfx4` opens `P_to_V` (the bundled eval-claim message).
- `theorem Spartan.Spec.Bricks.sfx3_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:146](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L146) — `sfx3 = ⟨P_to_V, EvalClaim⟩ ++ₚ sfx4` opens `P_to_V` (the bundled eval-claim message).
- `theorem Spartan.Spec.Bricks.sfx3_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:94](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L94) — `sfx3 = ⟨P_to_V, EvalClaim⟩ ++ₚ sfx4` opens `P_to_V` (the bundled eval-claim message).

### `sfx4_dir_seam` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx4_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:340](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L340) — Seam-direction fact for `linearCombination ▷ sfx5`: the combined spec (= `sfx4`) at the seam index `
- `theorem Spartan.Spec.Bricks.sfx4_dir_seam` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:135](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L135) — Seam-direction fact for `linearCombination ▷ sfx5`: the combined spec (= `sfx4`) at the seam index `
- `theorem Spartan.Spec.Bricks.sfx4_dir_seam` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:83](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L83) — Seam-direction fact for `linearCombination ▷ sfx5`: the combined spec (= `sfx4`) at the seam index `

### `sfx4_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx4_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:330](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L330) — `sfx4 = ⟨V_to_P, LinComb⟩ ++ₚ sfx5` opens `V_to_P` (the linear-combination challenge).
- `theorem Spartan.Spec.Bricks.sfx4_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:125](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L125) — `sfx4 = ⟨V_to_P, LinComb⟩ ++ₚ sfx5` opens `V_to_P` (the linear-combination challenge).
- `theorem Spartan.Spec.Bricks.sfx4_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:73](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L73) — `sfx4 = ⟨V_to_P, LinComb⟩ ++ₚ sfx5` opens `V_to_P` (the linear-combination challenge).

### `sfx5_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx5_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:319](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L319) — `sfx5 = !p[] ++ₚ sfx6` opens `P_to_V`. (Also the seam-direction fact for the `prependRLCTarget ▷ …`
- `theorem Spartan.Spec.Bricks.sfx5_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:112](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L112) — `sfx5 = !p[] ++ₚ sfx6` opens `P_to_V`. (Also the seam-direction fact for the `prependRLCTarget ▷ …`
- `theorem Spartan.Spec.Bricks.sfx5_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:62](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L62) — `sfx5 = !p[] ++ₚ sfx6` opens `P_to_V`. (Also the seam-direction fact for the `prependRLCTarget ▷ …`

### `sfx6_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sfx6_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:307](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L307) — `sfx6 = sumcheck₂ ++ₚ !p[]` opens `P_to_V` (second sum-check's leading message).
- `theorem Spartan.Spec.Bricks.sfx6_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:100](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L100) — `sfx6 = sumcheck₂ ++ₚ !p[]` opens `P_to_V` (second sum-check's leading message).
- `theorem Spartan.Spec.Bricks.sfx6_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:50](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L50) — `sfx6 = sumcheck₂ ++ₚ !p[]` opens `P_to_V` (second sum-check's leading message).

### `sumcheckPSpec_dir_zero` (3 declarations, 3 files)

- `theorem Spartan.Spec.Bricks.sumcheckPSpec_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:297](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L297) — The multi-round sum-check protocol opens with the prover's `P_to_V` polynomial message.
- `theorem Spartan.Spec.Bricks.sumcheckPSpec_dir_zero` [ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean:90](../../../ArkLib/ProofSystem/Spartan/ComposedRbrKnowledgeSoundness.lean#L90) — The multi-round sum-check protocol opens with the prover's `P_to_V` polynomial message.
- `theorem Spartan.Spec.Bricks.sumcheckPSpec_dir_zero` [ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean:40](../../../ArkLib/ProofSystem/Spartan/SpartanDirFacts.lean#L40) — The multi-round sum-check protocol opens with the prover's `P_to_V` polynomial message.

### `whose` (3 declarations, 3 files)

- `instance whose` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:19](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L19) — (no docstring)
- `theorem whose` [ArkLib/Data/CodingTheory/ProximityGap/BatchedFRIProof.lean:18](../../../ArkLib/Data/CodingTheory/ProximityGap/BatchedFRIProof.lean#L18) — (no docstring)
- `theorem whose` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:15](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L15) — (no docstring)

### `with` (3 declarations, 3 files)

- `theorem with` [ArkLib/Data/CodingTheory/ProximityGap/Hab25JohnsonDischarge.lean:31](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25JohnsonDischarge.lean#L31) — (no docstring)
- `instance with` [ArkLib/Data/CodingTheory/ProximityGap/LDAttainment.lean:32](../../../ArkLib/Data/CodingTheory/ProximityGap/LDAttainment.lean#L32) — (no docstring)
- `theorem with` [ArkLib/Data/CodingTheory/ProximityGap/PermanentlyBlocked.lean:55](../../../ArkLib/Data/CodingTheory/ProximityGap/PermanentlyBlocked.lean#L55) — (no docstring)

### `cast_id` (9 declarations, 2 files)

- `theorem Prover.cast_id` [ArkLib/OracleReduction/Cast.lean:53](../../../ArkLib/OracleReduction/Cast.lean#L53) — (no docstring)
- `theorem OracleProver.cast_id` [ArkLib/OracleReduction/Cast.lean:77](../../../ArkLib/OracleReduction/Cast.lean#L77) — (no docstring)
- `theorem Verifier.cast_id` [ArkLib/OracleReduction/Cast.lean:99](../../../ArkLib/OracleReduction/Cast.lean#L99) — (no docstring)
- `theorem Reduction.cast_id` [ArkLib/OracleReduction/Cast.lean:272](../../../ArkLib/OracleReduction/Cast.lean#L272) — (no docstring)
- `theorem ProtocolSpec.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:35](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L35) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:79](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L79) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:118](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L118) — (no docstring)
- `theorem ProtocolSpec.Transcript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:162](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L162) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:188](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L188) — (no docstring)

### `proj` (8 declarations, 2 files)

- `def Round16SelfSimilar.proj` [ArkLib/Data/CodingTheory/ProximityGap/SmoothDomainSelfSimilarity.lean:62](../../../ArkLib/Data/CodingTheory/ProximityGap/SmoothDomainSelfSimilarity.lean#L62) — The index fiber map `π : Fin (s·e) → Fin s`, `i ↦ i % s` (the index-level power map).
- `def Statement.Lens.proj` [ArkLib/OracleReduction/LiftContext/Lens.lean:49](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L49) — Transport input statements from the outer context to the inner context
- `def OracleStatement.Lens.proj` [ArkLib/OracleReduction/LiftContext/Lens.lean:109](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L109) — Transport input statements from the outer context to the inner context This is the projection compon
- `def Witness.Lens.proj` [ArkLib/OracleReduction/LiftContext/Lens.lean:236](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L236) — Transport input witness from the outer context to the inner context
- `def Context.Lens.proj` [ArkLib/OracleReduction/LiftContext/Lens.lean:263](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L263) — Projection of the context.
- `def OracleContext.Lens.proj` [ArkLib/OracleReduction/LiftContext/Lens.lean:300](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L300) — Projection of the context.
- `def Witness.InvLens.proj` [ArkLib/OracleReduction/LiftContext/Lens.lean:339](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L339) — Projection of the witness.
- `def Extractor.Lens.proj` [ArkLib/OracleReduction/LiftContext/Lens.lean:372](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L372) — Transport the tuple of (input statement, output witness) from the outer context to the inner context

### `seqCompose` (8 declarations, 2 files)

- `def Prover.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:37](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L37) — Sequential composition of provers, defined via iteration of the composition (append) of two provers.
- `def Verifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:75](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L75) — Sequential composition of verifiers, defined via iteration of the composition (append) of two verifi
- `def Reduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:104](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L104) — Sequential composition of reductions, defined via sequential composition of provers and verifiers (o
- `def OracleProver.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:135](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L135) — Sequential composition of provers in oracle reductions, defined via sequential composition of prover
- `def OracleVerifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:188](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L188) — Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the comp
- `def OracleReduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:310](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L310) — Sequential composition of oracle reductions, defined via sequential composition of oracle provers an
- `def ProtocolSpec.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:335](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L335) — Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`. Defined for definitio
- `def ProtocolSpec.FullTranscript.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:393](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L393) — Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`. Defined for definit

### `seqCompose_zero` (7 declarations, 2 files)

- `lemma Prover.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:48](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L48) — (no docstring)
- `lemma Verifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:83](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L83) — (no docstring)
- `lemma Reduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:113](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L113) — (no docstring)
- `lemma OracleVerifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:204](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L204) — (no docstring)
- `lemma OracleReduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:347](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L347) — (no docstring)
- `theorem ProtocolSpec.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:351](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L351) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:398](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L398) — (no docstring)

### `concat` (5 declarations, 2 files)

- `def ProtocolSpec.MessagesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:416](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L416) — Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming round `
- `def ProtocolSpec.ChallengesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:465](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L465) — Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming rou
- `abbrev ProtocolSpec.Transcript.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:504](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L504) — Concatenate a message to the end of a partial transcript. This is definitionally equivalent to `Fin.
- `abbrev ProtocolSpec.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:44](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L44) — Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec`
- `def ProtocolSpec.FullTranscript.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:168](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L168) — Adding a message with a given direction and type to the end of a `Transcript`

### `knowledgeSoundness` (5 declarations, 2 files)

- `def Verifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:357](../../../ArkLib/OracleReduction/Security/Basic.lean#L357) — A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and wit
- `def OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:492](../../../ArkLib/OracleReduction/Security/Basic.lean#L492) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:533](../../../ArkLib/OracleReduction/Security/Basic.lean#L533) — (no docstring)
- `def OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:571](../../../ArkLib/OracleReduction/Security/Basic.lean#L571) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.knowledgeSoundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:195](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L195) — State-restoration knowledge soundness (w/ straightline extractor).

### `new` (5 declarations, 2 files)

- `def DomainSeparator.Op.new` [ArkLib/Data/Hash/DomainSep.lean:138](../../../ArkLib/Data/Hash/DomainSep.lean#L138) — Construct a new `Op` from a character `id` and a count number `count : Option Nat`. Returns error if
- `def DomainSeparator.new` [ArkLib/Data/Hash/DomainSep.lean:193](../../../ArkLib/Data/Hash/DomainSep.lean#L193) — Create a new DomainSeparator with the domain separator. Rust interface: ```rust pub fn new(session_i
- `def HashStateWithInstructions.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:98](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L98) — Initialize a stateful hash object from a domain separator. Rust interface: ```rust pub fn new(domain
- `def FSVerifierState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:275](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L275) — Create a new VerifierState from a domain separator and NARG string. Rust interface: ```rust pub fn n
- `def FSProverState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:416](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L416) — Create a new `FSProverState` from a domain separator and RNG. Rust interface: ```rust pub fn new(dom

### `perfectCompleteness` (5 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.perfectCompleteness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:66](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L66) — Paper-facing alias for CO25 Section 3.4 perfect completeness.
- `def Reduction.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:126](../../../ArkLib/OracleReduction/Security/Basic.lean#L126) — A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`.
- `def OracleReduction.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:472](../../../ArkLib/OracleReduction/Security/Basic.lean#L472) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:522](../../../ArkLib/OracleReduction/Security/Basic.lean#L522) — (no docstring)
- `def OracleProof.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:555](../../../ArkLib/OracleReduction/Security/Basic.lean#L555) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.

### `cast_eq_dcast₂` (4 declarations, 2 files)

- `theorem Verifier.cast_eq_dcast₂` [ArkLib/OracleReduction/Cast.lean:107](../../../ArkLib/OracleReduction/Cast.lean#L107) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:91](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L91) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:130](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L130) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:194](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L194) — (no docstring)

### `crossover_gt` (4 declarations, 2 files)

- `theorem R10ExactDelta.crossover_gt` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean:119](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean#L119) — Lower side: just below, at `a* - 1 = 3`, the list strictly exceeds `B = 10`.
- `theorem R11DeltaTable.Row1.crossover_gt` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:154](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L154) — Lower side: the list strictly exceeds `B` one step below.
- `theorem R11DeltaTable.Row2.crossover_gt` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:211](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L211) — Lower side: the list strictly exceeds `B` one step below.
- `theorem R11DeltaTable.Row3.crossover_gt` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:268](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L268) — Lower side: the list strictly exceeds `B` one step below.

### `crossover_le` (4 declarations, 2 files)

- `theorem R10ExactDelta.crossover_le` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean:116](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean#L116) — Upper side: at the crossover `a* = 4` the list fits the bound `B = 10`.
- `theorem R11DeltaTable.Row1.crossover_le` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:152](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L152) — Upper side: the list fits `B = 10` at the crossover.
- `theorem R11DeltaTable.Row2.crossover_le` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:209](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L209) — Upper side: the list fits `B = 10` at the crossover.
- `theorem R11DeltaTable.Row3.crossover_le` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:266](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L266) — Upper side: the list fits `B = 10` at the crossover.

### `instDCast₂` (4 declarations, 2 files)

- `instance Prover.instDCast₂` [ArkLib/OracleReduction/Cast.lean:60](../../../ArkLib/OracleReduction/Cast.lean#L60) — (no docstring)
- `instance ProtocolSpec.MessageIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:87](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L87) — (no docstring)
- `instance ProtocolSpec.ChallengeIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:126](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L126) — (no docstring)
- `instance ProtocolSpec.FullTranscript.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:190](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L190) — (no docstring)

### `interior` (4 declarations, 2 files)

- `theorem R10ExactDelta.interior` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean:125](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean#L125) — The crossover is strictly **interior** to the open prize window: `k < a*` (i.e. `δ* < 1 - k/n`, abov
- `theorem R11DeltaTable.Row1.interior` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:160](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L160) — The crossover is strictly interior: `k < a*` and `a*² < k·n` (`3 < 5` and `25 < 48 = 3·16`).
- `theorem R11DeltaTable.Row2.interior` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:217](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L217) — The crossover is strictly interior: `k < a*` and `a*² < k·n` (`2 < 3` and `9 < 16 = 2·8`).
- `theorem R11DeltaTable.Row3.interior` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:274](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L274) — The crossover is strictly interior: `k < a*` and `a*² < k·n` (`2 < 3` and `9 < 16 = 2·8`).

### `listSize` (4 declarations, 2 files)

- `def R10ExactDelta.listSize` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean:99](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactCrossoverF17.lean#L99) — The list size at agreement threshold `a`: number of lines `(b,c)` whose agreement with `w` is at lea
- `def R11DeltaTable.Row1.listSize` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:135](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L135) — `listSize a = \|Λ(C, δ)\|`, `δ = 1 - a/16`.
- `def R11DeltaTable.Row2.listSize` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:193](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L193) — `listSize a = \|Λ(C, δ)\|`, `δ = 1 - a/8`.
- `def R11DeltaTable.Row3.listSize` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean:250](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarTableSmoothInstances.lean#L250) — `listSize a = \|Λ(C, δ)\|`, `δ = 1 - a/8`.

### `subdomain` (4 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:88](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L88) — Given a smooth coset FFT domain `ω` of log-order `n` this function returns its subdomain of log-orde
- `abbrev Domain.CosetFftDomain.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:449](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L449) — (no docstring)
- `def Domain.FftDomainClass.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:44](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L44) — (no docstring)
- `abbrev Domain.FftDomain.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:134](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L134) — (no docstring)

### `toList` (4 declarations, 2 files)

- `def Domain.CosetFftDomainClass.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:37](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L37) — (no docstring)
- `def Domain.CosetFftDomain.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:52](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L52) — Convert a coset FFT domain into a list of all its members with proofs the members belong to the FFT
- `def Domain.FftDomain.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:63](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L63) — Convert a FFT domain into a list of all its members with proofs the members belong to the FFT domain
- `def ProtocolSpec.EncodedMessagesBefore.toList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L77) — Flatten to a sigma-list for consumers still expecting `List (Sigma ...)`.

### `D_injective` (3 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round3SmoothF17.D_injective` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:90](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L90) — The domain map is injective (it is an `Embedding`, but we record the underlying statement).
- `lemma RSDeltaStar.Concrete.D_injective` [ArkLib/Data/CodingTheory/ProximityGap/RSAveragingDeltaStarUpper.lean:280](../../../ArkLib/Data/CodingTheory/ProximityGap/RSAveragingDeltaStarUpper.lean#L280) — `D` is injective (so this is a genuine RS evaluation domain).
- `lemma RSDeltaStar.ConcretePos.D_injective` [ArkLib/Data/CodingTheory/ProximityGap/RSAveragingDeltaStarUpper.lean:363](../../../ArkLib/Data/CodingTheory/ProximityGap/RSAveragingDeltaStarUpper.lean#L363) — `D` is injective.

### `accepts` (3 declarations, 2 files)

- `def Plonk.Gate.accepts` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:58](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L58) — A gate accepts an input vector `x` if its evaluation at `x` is zero.
- `def Plonk.ConstraintSystem.accepts` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:129](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L129) — A constraint system accepts an input vector `x` if all of its gates accept `x`.
- `def ToyProblem.Spec.accepts` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:176](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L176) — The §6.1 decision predicate, factored out so completeness proofs and the verifier object share the s

### `advantage` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.advantage` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:409](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L409) — Weak-binding advantage.
- `def ArkLib.Lattices.SIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:62](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L62) — Search advantage for a SIS-style problem.
- `def ArkLib.Lattices.ModuleSIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:106](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L106) — The Module-SIS advantage.

### `domain` (3 declarations, 2 files)

- `def ArkLib.BoundaryCardResidualRefutation.domain` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualRefutation.lean:53](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualRefutation.lean#L53) — Four distinct evaluation points in `ZMod 5`.
- `def Fri.Domain.domain` [ArkLib/ProofSystem/Fri/Domain.lean:41](../../../ArkLib/ProofSystem/Fri/Domain.lean#L41) — Allows us to enumerate the elements of the subgroup defined above.
- `def Fri.CosetDomain.domain` [ArkLib/ProofSystem/Fri/Domain.lean:451](../../../ArkLib/ProofSystem/Fri/Domain.lean#L451) — (no docstring)

### `experiment` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.experiment` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:396](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L396) — The Hachi/Greyhound weak-binding experiment. ## Ordinary vs. weak binding *Ordinary (exact) binding*
- `def ArkLib.Lattices.SIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:56](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L56) — The SIS experiment: sample a challenge, run the adversary, check validity.
- `def ArkLib.Lattices.ModuleSIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:101](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L101) — The Module-SIS experiment.

### `extract` (3 declarations, 2 files)

- `def Fin.extract` [ArkLib/Data/Fin/Tuple/Defs.lean:73](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L73) — Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`.
- `def ProtocolSpec.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:137](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L137) — Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`.
- `abbrev ProtocolSpec.FullTranscript.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:194](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L194) — (no docstring)

### `fst` (3 declarations, 2 files)

- `def Prover.fst` [ArkLib/OracleReduction/Composition/Sequential/SeamDecomposition.lean:52](../../../ArkLib/OracleReduction/Composition/Sequential/SeamDecomposition.lean#L52) — **Phase-1 seam restriction of a (malicious) prover** over `pSpec₁ ++ₚ pSpec₂`. Runs rounds `0 .. m-1
- `def ProtocolSpec.Transcript.fst` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:132](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L132) — The first half of a partial transcript for a concatenated protocol, up to round `k < m + n + 1`. Thi
- `def ProtocolSpec.FullTranscript.fst` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:217](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L217) — The first half of a transcript for a concatenated protocol

### `mem_toFinset_iff_mem` (3 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:71](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L71) — (no docstring)
- `lemma Domain.CosetFftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:117](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L117) — (no docstring)
- `lemma Domain.FftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/FftDomain/Mem.lean:69](../../../ArkLib/Data/Domain/FftDomain/Mem.lean#L69) — (no docstring)

### `rdrop` (3 declarations, 2 files)

- `abbrev Fin.rdrop` [ArkLib/Data/Fin/Tuple/Defs.lean:68](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L68) — Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. This is defi
- `def ProtocolSpec.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:133](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L133) — Drop the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:190](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L190) — (no docstring)

### `rtake` (3 declarations, 2 files)

- `def Fin.rtake` [ArkLib/Data/Fin/Tuple/Defs.lean:55](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L55) — Take the last `m` elements of a finite vector
- `def ProtocolSpec.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:125](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L125) — Take the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:182](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L182) — Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec`

### `snd` (3 declarations, 2 files)

- `def Prover.snd` [ArkLib/OracleReduction/Composition/Sequential/SeamDecomposition.lean:90](../../../ArkLib/OracleReduction/Composition/Sequential/SeamDecomposition.lean#L90) — **Phase-2 seam restriction of a (malicious) prover** over `pSpec₁ ++ₚ pSpec₂`. Resumes from `P`'s se
- `def ProtocolSpec.Transcript.snd` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:141](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L141) — The second half of a partial transcript for a concatenated protocol.
- `def ProtocolSpec.FullTranscript.snd` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:223](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L223) — The second half of a transcript for a concatenated protocol

### `AntipodallyClosed` (2 declarations, 2 files)

- `def Round28FullWindow.AntipodallyClosed` [ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean:47](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean#L47) — An antipodally-closed finset: `x ∈ A ⟹ −x ∈ A`, with `0 ∉ A`.
- `def Round26Recursion.AntipodallyClosed` [ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean:45](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean#L45) — An antipodally-closed finset: `x ∈ A ⟹ −x ∈ A`, with `0 ∉ A`.

### `BindingAdversary` (2 declarations, 2 files)

- `structure Commitment.BindingAdversary` [ArkLib/CommitmentScheme/Basic.lean:116](../../../ArkLib/CommitmentScheme/Basic.lean#L116) — An adversary in the (evaluation) binding game returns a commitment `cm`, a query `q`, two purported
- `structure CommitmentScheme.BindingAdversary` [ArkLib/CommitmentScheme/CommitmentScheme.lean:89](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L89) — An adversary in the binding game returns a commitment and two purported openings to possibly differe

### `ChallengeIdx` (2 declarations, 2 files)

- `def ProtocolSpec.ChallengeIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:66](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L66) — Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification
- `def ProtocolSpec.VectorSpec.ChallengeIdx` [ArkLib/OracleReduction/VectorIOR.lean:54](../../../ArkLib/OracleReduction/VectorIOR.lean#L54) — The type of indices for challenges in a `VectorSpec`.

### `Codec` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.Codec` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:204](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L204) — Paper-facing alias for CO25 Definition 4.1 codecs.
- `class ProtocolSpec.Codec` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:99](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L99) — Codec class for CO25 Definition 4.1. `Codec pSpec U` is the generic-parameter carrier for everything

### `Commit` (2 declarations, 2 files)

- `structure Commitment.Commit` [ArkLib/CommitmentScheme/Basic.lean:53](../../../ArkLib/CommitmentScheme/Basic.lean#L53) — The commitment algorithm, parameterized by the committer key and the data to commit.
- `structure CommitmentScheme.Commit` [ArkLib/CommitmentScheme/CommitmentScheme.lean:38](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L38) — The commitment algorithm, returning both the commitment and its opening value.

### `Commitment` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Commitment` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:126](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L126) — Inner-outer commitments live in the outer row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Commitment` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:35](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L35) — Commitments: row vectors over `Rq Φ`.

### `ConstraintSystem` (2 declarations, 2 files)

- `structure ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:49](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L49) — A **constraint system** packages a family of indexed relations into a single bundle. For each `i : I
- `def Plonk.ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:116](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L116) — A Plonk constraint system is a vector of `numGates` gates, each parametrized by the underlying ring

### `CurveCaptured` (2 declarations, 2 files)

- `def CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.CurveCaptured` [ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCapture.lean:158](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCapture.lean#L158) — **The `L`-ary capture predicate** (mirrors `AffineCaptured`): the polynomial curve `∑ⱼ C(γʲ)·aⱼ` mat
- `def MutualCorrAgreement.CurveCaptured` [ArkLib/ProofSystem/Whir/MCAConjectureEllaryReduction.lean:178](../../../ArkLib/ProofSystem/Whir/MCAConjectureEllaryReduction.lean#L178) — **ℓ-ary curve capture.** The bad scalar `γ` is captured by the polynomial tuple `a : Fin L → F[X]` w

### `CurveCoeffPolys` (2 declarations, 2 files)

- `def ArkLib.BetaToCurveCoeffPolys.CurveCoeffPolys` [ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean:100](../../../ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean#L100) — Asserts that each coefficient of the decoded polynomial $P(z)$ at index $j < deg$ is interpolated by
- `def ArkLib.KeystoneCapstone.CurveCoeffPolys` [ArkLib/ToMathlib/KeystoneCapstone.lean:92](../../../ArkLib/ToMathlib/KeystoneCapstone.lean#L92) — (no docstring)

### `CurveDecodable` (2 declarations, 2 files)

- `def ProximityGap.CurveDec.CurveDecodable` [ArkLib/Data/CodingTheory/ProximityGap/CurveDecodability.lean:110](../../../ArkLib/Data/CodingTheory/ProximityGap/CurveDecodability.lean#L110) — **[GG25] Definition 3.1 ([Jo26] Definition 2.7): curve decodability.**  `C` is `(ℓ, δ, a, b)`-curve-
- `def ProximityGap.CurveDecodable` [ArkLib/Data/CodingTheory/ProximityGap/GG25CurveDecodability.lean:59](../../../ArkLib/Data/CodingTheory/ProximityGap/GG25CurveDecodability.lean#L59) — **[GG25] Definition 3.1 / [Jo26] Definition 2.7 (curve decodability).** `C` is `(ℓ, δ, a, b)`-curve-

### `CurveFamilyProducer` (2 declarations, 2 files)

- `abbrev ArkLib.ClosedBoundaryFaithfulFloorCell.CurveFamilyProducer` [ArkLib/ToMathlib/ClosedBoundaryFaithfulFloorCell.lean:113](../../../ArkLib/ToMathlib/ClosedBoundaryFaithfulFloorCell.lean#L113) — **The faithful per-`(u, P)` §5 producer at radius `δ`** — exactly the `hInput` shape of `FaithfulCur
- `abbrev ArkLib.FaithfulCurveExtraction.RoundConsumers.CurveFamilyProducer` [ArkLib/ToMathlib/CurveFamilyRoundConsumers.lean:77](../../../ArkLib/ToMathlib/CurveFamilyRoundConsumers.lean#L77) — **The per-`(u, P)` faithful curve-family producer at one round's parameters.**  This is exactly the

### `E_col_p` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_col_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:261](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L261) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_col_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:237](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L237) — (no docstring)

### `E_col_p_pinv` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_col_p_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:279](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L279) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_col_p_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:255](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L255) — (no docstring)

### `E_col_pinv` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_col_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:270](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L270) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_col_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:246](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L246) — (no docstring)

### `E_col_pinv_p` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_col_pinv_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:288](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L288) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_col_pinv_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:264](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L264) — (no docstring)

### `E_dup` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_dup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:211](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L211) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_dup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:187](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L187) — (no docstring)

### `E_func` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_func` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:223](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L223) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_func` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:199](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L199) — (no docstring)

### `E_h` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_h` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:166](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L166) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_h` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:142](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L142) — (no docstring)

### `E_p` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:185](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L185) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:161](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L161) — (no docstring)

### `E_pinv` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:204](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L204) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:180](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L180) — (no docstring)

### `E_prp` (2 declarations, 2 files)

- `alias OracleSpec.QueryLog.BadEventDS.E_prp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:293](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L293) — (no docstring)
- `alias OracleSpec.QueryLog.BadEventDSPaper.E_prp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:269](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L269) — (no docstring)

### `ExtractabilityAdversary` (2 declarations, 2 files)

- `abbrev Commitment.ExtractabilityAdversary` [ArkLib/CommitmentScheme/Basic.lean:183](../../../ArkLib/CommitmentScheme/Basic.lean#L183) — An adversary in the extractability game is an oracle computation that returns a commitment, a query,
- `structure CommitmentScheme.ExtractabilityAdversary` [ArkLib/CommitmentScheme/CommitmentScheme.lean:137](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L137) — An adversary in the extractability game returns a commitment, a claimed message/opening pair, and au

### `FinalOracleStatement` (2 declarations, 2 files)

- `def Fri.Spec.FinalOracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:97](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L97) — (no docstring)
- `def Spartan.Spec.Bricks.FinalOracleStatement` [ArkLib/ToMathlib/SpartanBricks.lean:102](../../../ArkLib/ToMathlib/SpartanBricks.lean#L102) — The terminal oracle-statement family: unchanged from after the second sum-check (`bundled (v_A,v_B,v

### `FinalStatement` (2 declarations, 2 files)

- `def Fri.Spec.FinalStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:83](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L83) — (no docstring)
- `def Spartan.Spec.Bricks.FinalStatement` [ArkLib/ToMathlib/SpartanBricks.lean:97](../../../ArkLib/ToMathlib/SpartanBricks.lean#L97) — The terminal claim statement type: the full Spartan statement after the second sum-check (`(r_y, (r_

### `G_eighth_roots` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyF17.G_eighth_roots` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyF17.lean:49](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyF17.lean#L49) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupRepCountFiniteFieldCounterexample.G_eighth_roots` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupRepCountFiniteFieldCounterexample.lean:48](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupRepCountFiniteFieldCounterexample.lean#L48) — Every element of `G` is an `8`-th root of unity (`x^8 = 1`).

### `GenMutualCorrParams` (2 declarations, 2 files)

- `class Fold.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/Folding.lean:683](../../../ArkLib/ProofSystem/Whir/Folding.lean#L683) — The `GenMutualCorrParams` class captures the necessary parameters and assumptions to model a sequenc
- `class WhirIOP.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:85](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L85) — `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes `C_{i : M + 1, j : foldingPar

### `H16` (2 declarations, 2 files)

- `def ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257.H16` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat257.lean:61](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat257.lean#L61) — Order-16 subgroup of `F₂₅₇^×`.
- `def ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537.H16` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat65537.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat65537.lean#L51) — Order-16 subgroup of `F₆₅₅₃₇^×`.

### `H_tilde_monic` (2 declarations, 2 files)

- `lemma BCIKS20AppendixA.H_tilde_monic` [ArkLib/Data/Polynomial/RationalFunctionsCore.lean:1216](../../../ArkLib/Data/Polynomial/RationalFunctionsCore.lean#L1216) — The monicized polynomial `H_tilde H` is monic, as the image of the monic `H_tilde' H`.
- `theorem BCIKS20.ZLinearRatFuncDegreeOne.H_tilde_monic` [ArkLib/ToMathlib/ZLinearRatFuncDegreeOne.lean:194](../../../ArkLib/ToMathlib/ZLinearRatFuncDegreeOne.lean#L194) — The monicized modulus `H̃` is monic (map of the monic `H̃'`).

### `Hypercube` (2 declarations, 2 files)

- `def ArkLib.CodingTheory.Research.Hypercube` [ArkLib/Data/CodingTheory/Quarantine/MultilinearHypercube.lean:20](../../../ArkLib/Data/CodingTheory/Quarantine/MultilinearHypercube.lean#L20) — The Boolean Hypercube domain defined over the field F.
- `def Logup.Hypercube` [ArkLib/ProofSystem/Logup/Common.lean:35](../../../ArkLib/ProofSystem/Logup/Common.lean#L35) — The boolean hypercube with `2^n` points. The paper writes this domain as `H = {±1}^n`; we use bit ve

### `KeyGen` (2 declarations, 2 files)

- `structure Commitment.KeyGen` [ArkLib/CommitmentScheme/Basic.lean:49](../../../ArkLib/CommitmentScheme/Basic.lean#L49) — Key generation for a commitment scheme, producing a committer key and a verifier key.
- `structure CommitmentScheme.KeyGen` [ArkLib/CommitmentScheme/CommitmentScheme.lean:34](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L34) — The key-generation algorithm, returning separate keys for the committer and verifier.

### `L11` (2 declarations, 2 files)

- `def ArkLib.CodingTheory.TinyInteriorF11.L11` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11.lean:105](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11.lean#L105) — The candidate list `L₁₁ = {d0, …, d14}`.
- `def ProximityGap.MissingLineDefeater.L11` [ArkLib/Data/CodingTheory/ProximityGap/MissingLineDefeater.lean:107](../../../ArkLib/Data/CodingTheory/ProximityGap/MissingLineDefeater.lean#L107) — (no docstring)

### `MLE_eval_eq_sum_eqTilde` (2 declarations, 2 files)

- `theorem MvPolynomial.MLE_eval_eq_sum_eqTilde` [ArkLib/Data/MvPolynomial/Multilinear.lean:319](../../../ArkLib/Data/MvPolynomial/Multilinear.lean#L319) — **MLE evaluation as an eq-weighted sum over the hypercube.**  Evaluating the multilinear extension a
- `lemma RingSwitching.MLE_eval_eq_sum_eqTilde` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1119](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1119) — **MLE evaluation as an `eq̃`-weighted hypercube sum.** Evaluating the multilinear extension `MLE f`

### `MarkedCurveDecodable` (2 declarations, 2 files)

- `def ProximityGap.CurveDec.MarkedCurveDecodable` [ArkLib/Data/CodingTheory/ProximityGap/CurveDecodability.lean:121](../../../ArkLib/Data/CodingTheory/ProximityGap/CurveDecodability.lean#L121) — **[Jo26] Definition 5.1: marked curve decodability.**  Same data, but quantified over an arbitrary *
- `def ProximityGap.MarkedCurveDecodable` [ArkLib/Data/CodingTheory/ProximityGap/GG25MarkedCurve.lean:59](../../../ArkLib/Data/CodingTheory/ProximityGap/GG25MarkedCurve.lean#L59) — **[Jo26] Definition 5.1 (marked curve decodability).** For every stack, every codeword-valued `f`, a

### `MessageIdx` (2 declarations, 2 files)

- `def ProtocolSpec.MessageIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:61](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L61) — Subtype of `Fin n` for the indices corresponding to messages in a protocol specification
- `def ProtocolSpec.VectorSpec.MessageIdx` [ArkLib/OracleReduction/VectorIOR.lean:50](../../../ArkLib/OracleReduction/VectorIOR.lean#L50) — The type of indices for messages in a `VectorSpec`.

### `NoRedundantEntryDSPaper` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.NoRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:57](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L57) — A trace has no paper-redundant entries.
- `def DuplexSpongeFS.Paper.NoRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L67) — No entry of the trace is paper-redundant.

### `OStmt` (2 declarations, 2 files)

- `def StirIOP.Round.OStmt` [ArkLib/ProofSystem/Stir/RoundProtocol.lean:53](../../../ArkLib/ProofSystem/Stir/RoundProtocol.lean#L53) — The single-index oracle statement family for a STIR fold round: the prover holds one oracle function
- `def WhirIOP.Construction.OStmt` [ArkLib/ToMathlib/WhirBricksConstruction.lean:49](../../../ArkLib/ToMathlib/WhirBricksConstruction.lean#L49) — The single-index oracle statement family for the WHIR Vector IOPP: the prover holds one oracle funct

### `OracleProver` (2 declarations, 2 files)

- `abbrev Interaction.OracleDecoration.OracleProver` [ArkLib/Interaction/Oracle/Core.lean:898](../../../ArkLib/Interaction/Oracle/Core.lean#L898) — (no docstring)
- `def OracleProver` [ArkLib/OracleReduction/Basic.lean:446](../../../ArkLib/OracleReduction/Basic.lean#L446) — An **(oracle) prover** in an interactive **oracle** reduction is a prover in the non-oracle reductio

### `OracleReduction` (2 declarations, 2 files)

- `structure Interaction.OracleDecoration.OracleReduction` [ArkLib/Interaction/Oracle/Core.lean:928](../../../ArkLib/Interaction/Oracle/Core.lean#L928) — (no docstring)
- `structure OracleReduction` [ArkLib/OracleReduction/Basic.lean:768](../../../ArkLib/OracleReduction/Basic.lean#L768) — An **interactive oracle reduction** for a given protocol specification `pSpec`, and relative to orac

### `OracleVerifier` (3 declarations, 2 files)

- `structure Interaction.OracleVerifier` [ArkLib/Interaction/Oracle/Core.lean:1042](../../../ArkLib/Interaction/Oracle/Core.lean#L1042) — (no docstring)
- `structure OracleVerifier` [ArkLib/OracleReduction/Basic.lean:175](../../../ArkLib/OracleReduction/Basic.lean#L175) — (no docstring)
- `structure OracleVerifier` [ArkLib/OracleReduction/Basic.lean:466](../../../ArkLib/OracleReduction/Basic.lean#L466) — An **(oracle) verifier** of an interactive **oracle** reduction consists of: - an oracle computation

### `OuterRunSamplesChallenge` (2 declarations, 2 files)

- `def OuterRunSamplesChallenge` [ArkLib/ProofSystem/Logup/Security/OuterRunSamplesChallenge.lean:24](../../../ArkLib/ProofSystem/Logup/Security/OuterRunSamplesChallenge.lean#L24) — (no docstring)
- `def Logup.OuterRunSamplesChallenge` [ArkLib/ProofSystem/Logup/Security/OuterSoundnessReal.lean:224](../../../ArkLib/ProofSystem/Logup/Security/OuterSoundnessReal.lean#L224) — **The genuine residual interface: the outer run samples the challenge.** This is the *only* gap betw

### `OutputOracleStatement` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:116](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L116) — Output oracle statement: the IOR has no output oracle component.
- `def ToyProblem.SimplifiedIOR.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:77](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L77) — Output oracle statement: the single combined codeword `f_new := f₁ + γ·f₂ : ι → F`.

### `OutputWitness` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:120](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L120) — Output witness: empty.
- `def ToyProblem.SimplifiedIOR.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:81](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L81) — Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`.

### `ParamConditions` (2 declarations, 2 files)

- `structure StirIOP.ParamConditions` [ArkLib/ProofSystem/Stir/MainThm.lean:55](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L55) — **Conditions that protocol parameters must satisfy.** - `h_deg` : initial degree `deg` is a power of
- `structure WhirIOP.ParamConditions` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:66](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L66) — ** Conditions that protocol parameters must satisfy. ** h_m : m = varCount₀ h_sumkLt : ∑ i : Fin (M

### `PerRoundProximityGap` (2 declarations, 2 files)

- `def ArkLib.ProofSystem.Stir.ErrorAccumulation.PerRoundProximityGap` [ArkLib/ProofSystem/Stir/ErrorAccumulation.lean:307](../../../ArkLib/ProofSystem/Stir/ErrorAccumulation.lean#L307) — The keystone, abstracted. `PerRoundProximityGap e ProxGapBound` says the accounting per-round error
- `def Core2Keystone.PerRoundProximityGap` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:52](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L52) — Verbatim copy of `Issue24FRISTIR.PerRoundProximityGap` (`Stir/SoundnessAccumulation.lean:253`): the

### `Pr_badStack_eq_one` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.Pr_badStack_eq_one` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean:64](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean#L64) — **The bad event has probability 1.** Since `mcaEventGSrow_badStack` holds for every `γ`, the event i
- `theorem Pr_badStack_eq_one` [ArkLib/MCAGSRefutationCore.lean:63](../../../ArkLib/MCAGSRefutationCore.lean#L63) — **The bad event has probability 1.** Since `mcaEventGSrow_badStack` holds for every `γ`, the event i

### `Proof` (2 declarations, 2 files)

- `abbrev Interaction.Proof` [ArkLib/Interaction/Reduction.lean:232](../../../ArkLib/Interaction/Reduction.lean#L232) — (no docstring)
- `def Proof` [ArkLib/OracleReduction/Basic.lean:792](../../../ArkLib/OracleReduction/Basic.lean#L792) — An **interactive proof (IP)** is an interactive reduction where the output statement is a boolean, t

### `RS_correlatedAgreement_affineLines` (2 declarations, 2 files)

- `theorem ProximityGap.RS_correlatedAgreement_affineLines` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean:52](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean#L52) — Theorem 1.4 (Main Theorem — Correlated agreement over lines) in [BCIKS20]. Take a Reed-Solomon code
- `theorem RS_correlatedAgreement_affineLines` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualAffineLineRefutation.lean:19](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualAffineLineRefutation.lean#L19) — (no docstring)

### `RewindingExtractor` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.RewindingExtractor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:155](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L155) — Paper-facing alias for the rewinding extractor interface from CO25 Definition 3.8.
- `def Extractor.RewindingExtractor` [ArkLib/ToMathlib/RewindingExtractor.lean:115](../../../ArkLib/ToMathlib/RewindingExtractor.lean#L115) — A **rewinding extractor** for the 2-special-sound case: given the recorded prefix and **two** comple

### `Scheme` (2 declarations, 2 files)

- `structure Commitment.Scheme` [ArkLib/CommitmentScheme/Basic.lean:64](../../../ArkLib/CommitmentScheme/Basic.lean#L64) — A commitment scheme with key generation, commitment, and opening algorithms.
- `structure CommitmentScheme.Scheme` [ArkLib/CommitmentScheme/CommitmentScheme.lean:46](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L46) — An ordinary commitment scheme.

### `SpongeState` (2 declarations, 2 files)

- `class SpongeState` [ArkLib/Data/Hash/DuplexSponge.lean:255](../../../ArkLib/Data/Hash/DuplexSponge.lean#L255) — Type class for the state of a cryptographic permutation used in the duplex sponge construction. Rust
- `abbrev DuplexSpongeFS.SpongeState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:42](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L42) — Paper-facing alias for the canonical duplex-sponge state used in CO25 Section 3.3.

### `SumcheckLensProjComplete` (2 declarations, 2 files)

- `def Logup.SumcheckLensProjComplete` [ArkLib/ProofSystem/Logup/Security/SumcheckCompletenessClose.lean:100](../../../ArkLib/ProofSystem/Logup/Security/SumcheckCompletenessClose.lean#L100) — **The `proj_complete` half of `OracleContext.Lens.IsComplete` for the LogUp sum-check lens.** Every
- `def SumcheckLensProjComplete` [ArkLib/ProofSystem/Logup/Security/SumcheckLensProjComplete.lean:16](../../../ArkLib/ProofSystem/Logup/Security/SumcheckLensProjComplete.lean#L16) — (no docstring)

### `SumcheckMultiplierParam` (2 declarations, 2 files)

- `structure Sumcheck.Structured.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured.lean:85](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L85) — Parameters describing how the round polynomial `H` is built from the witness `t`: `H = P · Q(t)`, wh
- `structure Sumcheck.Structured.Prismalinear.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:50](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L50) — Parameters describing how a *prismalinear* round polynomial `H = P · Q(t)` is built from the witness

### `SumcheckWitness` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckWitness` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:237](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L237) — (no docstring)
- `structure Sumcheck.Structured.SumcheckWitness` [ArkLib/ProofSystem/Sumcheck/Structured.lean:231](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L231) — Witness for the structured sumcheck at round `i`: - `t'` — the original multilinear polynomial (the

### `TranscriptSimulator` (2 declarations, 2 files)

- `abbrev OracleReduction.TranscriptSimulator` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:38](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L38) — Transcript simulators for oracle reductions are simulators for the associated non-oracle reduction,
- `def Reduction.TranscriptSimulator` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:62](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L62) — A transcript simulator produces, from the input statement alone, a distribution over full transcript

### `UDRClose_of_fin_eq` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.UDRClose_of_fin_eq` [ArkLib/ProofSystem/Binius/BinaryBasefold/Reconstruct/UDRCongruence.lean:52](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Reconstruct/UDRCongruence.lean#L52) — **UDR-closeness congruence under domain-index equality.** If the domain indices `i, j : Fin r` are e
- `theorem Binius.BinaryBasefold.CoreInteraction.UDRClose_of_fin_eq` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:747](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L747) — Transport `UDRClose` across an index equality and a heterogeneous function equality.

### `Verifier.run` (2 declarations, 2 files)

- `def Interaction.Verifier.run` [ArkLib/Interaction/Reduction.lean:262](../../../ArkLib/Interaction/Reduction.lean#L262) — (no docstring)
- `def Verifier.run` [ArkLib/OracleReduction/Execution.lean:137](../../../ArkLib/OracleReduction/Execution.lean#L137) — Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and the t

### `WhirRbrKeystone` (2 declarations, 2 files)

- `def Core2Keystone.WhirRbrKeystone` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:80](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L80) — Verbatim copy of `Issue113WHIR.WhirRbrKeystone` (`Whir/RbrBudgetAccounting.lean:238`): the `SoundOk`
- `def Issue113WHIR.WhirRbrKeystone` [ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean:253](../../../ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean#L253) — **Named residual (the genuine open per-round soundness math).** `WhirRbrKeystone` abstracts the per-

### `WitIn` (2 declarations, 2 files)

- `def RandomQuery.WitIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:39](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L39) — (no docstring)
- `def Logup.WitIn` [ArkLib/ProofSystem/Logup/Common.lean:368](../../../ArkLib/ProofSystem/Logup/Common.lean#L368) — Protocol 2 has no private witness beyond the input oracles at this layer.

### `agree_add_hammingDist` (2 declarations, 2 files)

- `theorem CodeGeometry.agree_add_hammingDist` [ArkLib/Data/CodingTheory/CodeGeometry.lean:42](../../../ArkLib/Data/CodingTheory/CodeGeometry.lean#L42) — Agreement and Hamming distance partition the coordinate set.
- `theorem ArkLib.JohnsonBound.agree_add_hammingDist` [ArkLib/Data/CodingTheory/JohnsonBound/ListSize.lean:57](../../../ArkLib/Data/CodingTheory/JohnsonBound/ListSize.lean#L57) — Agreement plus Hamming distance equals the block length.

### `agreement` (2 declarations, 2 files)

- `def R14Derand.agreement` [ArkLib/Data/CodingTheory/ProximityGap/DerandomizationFrontier.lean:61](../../../ArkLib/Data/CodingTheory/ProximityGap/DerandomizationFrontier.lean#L61) — Absolute agreement: the number of coordinates where two words coincide.
- `def Round16SelfSimilar.agreement` [ArkLib/Data/CodingTheory/ProximityGap/SmoothDomainSelfSimilarity.lean:129](../../../ArkLib/Data/CodingTheory/ProximityGap/SmoothDomainSelfSimilarity.lean#L129) — Agreement count of a polynomial `g` with a word `w` over a domain `D`.

### `agreement_card_le` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.KKH26.agreement_card_le` [ArkLib/Data/CodingTheory/ProximityGap/KKH26CensusLaw.lean:102](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26CensusLaw.lean#L102) — **Rigidity: the agreement set of a bad scalar has size at most `r`.** The difference is monic of deg
- `theorem ArkLib.CodingTheory.UniqueDecoding.agreement_card_le` [ArkLib/Data/CodingTheory/ProximityGap/UniqueDecodingListBound.lean:84](../../../ArkLib/Data/CodingTheory/ProximityGap/UniqueDecodingListBound.lean#L84) — **Agreement bound.** Two distinct polynomials of degree `< k` evaluated on an injective domain agree

### `all_agree_ge_three` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.TinyInteriorPin.all_agree_ge_three` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:148](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L148) — **Interior agreement.** Every codeword in `L` agrees with the received word `w` on `≥ 3` coordinates
- `theorem ArkLib.CodingTheory.Round3SmoothF17.all_agree_ge_three` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:181](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L181) — **Interior agreement.** Every codeword in `L` agrees with the received word `w` on `≥ 3` coordinates

### `answer_instDefault` (2 declarations, 2 files)

- `lemma RingSwitching.BatchingPhase.answer_instDefault` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:66](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L66) — The default oracle interface (`OracleInterface.instDefault`, used by the ring-switching message orac
- `lemma ToyProblem.Spec.answer_instDefault` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:628](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L628) — `answer` of the default oracle interface is the identity (the message itself).

### `answer_instDefault'` (2 declarations, 2 files)

- `lemma RingSwitching.SumcheckPhase.answer_instDefault'` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:87](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L87) — The `instDefault` oracle answer is the message itself (`answer m () = m`).
- `lemma Fri.Spec.Completeness.answer_instDefault'` [ArkLib/ToMathlib/FriCompleteFinalRound.lean:86](../../../ArkLib/ToMathlib/FriCompleteFinalRound.lean#L86) — The default oracle interface answers its only (unit) query with the message itself (local copy of `R

### `appendRbrKnowledgeSoundnessResidual_msg_subsingleton` (2 declarations, 2 files)

- `theorem OracleVerifier.appendRbrKnowledgeSoundnessResidual_msg_subsingleton` [ArkLib/OracleReduction/Composition/Sequential/AppendRbrKnowledgeOracleLift.lean:94](../../../ArkLib/OracleReduction/Composition/Sequential/AppendRbrKnowledgeOracleLift.lean#L94) — **Discharge of the named residual `OracleVerifier.appendRbrKnowledgeSoundnessResidual`** (`Append.le
- `theorem Verifier.appendRbrKnowledgeSoundnessResidual_msg_subsingleton` [ArkLib/OracleReduction/Composition/Sequential/AppendResidualDischarges.lean:93](../../../ArkLib/OracleReduction/Composition/Sequential/AppendResidualDischarges.lean#L93) — **Discharge of the named residual `Verifier.appendRbrKnowledgeSoundnessResidual`** (deterministic-`V

### `appendRbrSoundnessResidual_msg_subsingleton` (2 declarations, 2 files)

- `theorem OracleVerifier.appendRbrSoundnessResidual_msg_subsingleton` [ArkLib/OracleReduction/Composition/Sequential/AppendRbrSoundnessOracleLift.lean:91](../../../ArkLib/OracleReduction/Composition/Sequential/AppendRbrSoundnessOracleLift.lean#L91) — **Discharge of the named residual `OracleVerifier.appendRbrSoundnessResidual`** (`Append.lean`) in t
- `theorem Verifier.appendRbrSoundnessResidual_msg_subsingleton` [ArkLib/OracleReduction/Composition/Sequential/AppendRbrSoundnessPhase2Proof.lean:639](../../../ArkLib/OracleReduction/Composition/Sequential/AppendRbrSoundnessPhase2Proof.lean#L639) — **Discharge of the named residual `Verifier.appendRbrSoundnessResidual`** (`Append.lean`) in the det

### `appendRight` (2 declarations, 2 files)

- `def Interaction.OracleDecoration.QueryHandle.appendRight` [ArkLib/Interaction/Oracle/Core.lean:202](../../../ArkLib/Interaction/Oracle/Core.lean#L202) — (no docstring)
- `def ProtocolSpec.Transcript.appendRight` [ArkLib/OracleReduction/ProtocolSpec/TranscriptRecompose.lean:56](../../../ArkLib/OracleReduction/ProtocolSpec/TranscriptRecompose.lean#L56) — Append a full `pSpec₁` transcript and a *partial* `pSpec₂` transcript into a partial transcript for

### `append_completeness_msg` (3 declarations, 2 files)

- `theorem Reduction.append_completeness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean:211](../../../ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean#L211) — **The error-bearing message-seam append-completeness keystone — no residual hypothesis.** For a mess
- `theorem OracleReduction.append_completeness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean:262](../../../ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean#L262) — **Oracle-level error-bearing append completeness — UNCONDITIONAL (message seam).** Completeness (err
- `theorem Reduction.append_completeness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean:254](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean#L254) — **Non-perfect (error-bearing) message-seam append completeness — fully discharged.** From the compon

### `append_completeness_msg_proof` (2 declarations, 2 files)

- `theorem Reduction.append_completeness_msg_proof` [ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessNonPerfect.lean:133](../../../ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessNonPerfect.lean#L133) — **NON-PERFECT (error-bearing) message-seam append completeness — discharged modulo the named two-sta
- `theorem OracleReduction.append_completeness_msg_proof` [ArkLib/ProofSystem/Logup/Security/LogupCompletenessWired.lean:117](../../../ArkLib/ProofSystem/Logup/Security/LogupCompletenessWired.lean#L117) — **Oracle-level non-perfect append completeness keystone (message seam) — verifier bridge discharged

### `append_left_injective` (2 declarations, 2 files)

- `theorem Fin.append_left_injective` [ArkLib/Data/Fin/Basic.lean:262](../../../ArkLib/Data/Fin/Basic.lean#L262) — (no docstring)
- `theorem ProtocolSpec.append_left_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:68](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L68) — (no docstring)

### `append_perfectCompleteness_challenge` (2 declarations, 2 files)

- `theorem Reduction.append_perfectCompleteness_challenge` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessChallenge.lean:255](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessChallenge.lean#L255) — **Challenge-seam append perfect completeness.** The `V_to_P`-seam analogue of `append_perfectComplet
- `theorem OracleReduction.append_perfectCompleteness_challenge` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessOracleChallenge.lean:54](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessOracleChallenge.lean#L54) — **Oracle-level challenge-seam append perfect completeness.** The `V_to_P` analogue of `append_perfec

### `append_perfectCompleteness_msg_proof` (2 declarations, 2 files)

- `theorem OracleReduction.append_perfectCompleteness_msg_proof` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessOracle.lean:81](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessOracle.lean#L81) — **Oracle-level perfect-completeness keystone (message seam).** Perfect completeness of `R₁.append R₂
- `theorem Reduction.append_perfectCompleteness_msg_proof` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessProof.lean:108](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessProof.lean#L108) — (no docstring)

### `append_right_injective` (2 declarations, 2 files)

- `theorem Fin.append_right_injective` [ArkLib/Data/Fin/Basic.lean:270](../../../ArkLib/Data/Fin/Basic.lean#L270) — (no docstring)
- `theorem ProtocolSpec.append_right_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:78](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L78) — (no docstring)

### `append_soundness_msg` (2 declarations, 2 files)

- `theorem Verifier.append_soundness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean:464](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean#L464) — **Unconditional binary append-soundness, message-seam case** (the conclusion of `Verifier.append_sou
- `theorem OracleVerifier.append_soundness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessOracleMsg.lean:62](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessOracleMsg.lean#L62) — **OracleVerifier-level plain-soundness append keystone, message seam (unconditional).** The appended

### `askInput` (2 declarations, 2 files)

- `def StirIOP.MultiRound.askInput` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:141](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L141) — Query the input codeword oracle at a domain point.
- `def Whir302Checked.askInput` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:67](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L67) — Query the public WHIR input oracle at an outer-domain point.

### `askList` (2 declarations, 2 files)

- `def StirIOP.MultiRound.askList` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:157](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L157) — Monadic map over a list with definitional `nil`/`cons` equations (avoiding `List.mapM`'s tail-recurs
- `def Whir302Checked.askList` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:102](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L102) — Monadic map over a list with definitional `nil`/`cons` equations (avoiding `List.mapM`'s tail-recurs

### `askMsg` (2 declarations, 2 files)

- `def StirIOP.MultiRound.askMsg` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:148](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L148) — Query the `j`-th prover message oracle at a vector position.
- `def Whir302Checked.askMsg` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:56](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L56) — Query the `j`-th prover message oracle at a vector position.

### `averaging_crossover` (2 declarations, 2 files)

- `theorem R10Bracket.averaging_crossover` [ArkLib/Data/CodingTheory/ProximityGap/BestProvableBracket.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/BestProvableBracket.lean#L51) — AVERAGING crossover. If the averaging list lower bound `maxList * q^t ≥ C(n,a)` holds (i.e. `maxList
- `theorem ArkLib.CodingTheory.Round9Bracket.averaging_crossover` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarAveragingBracket.lean:45](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarAveragingBracket.lean#L45) — **Averaging crossover (arithmetic core).** Given the pigeonhole averaging bound `C(n, k+t) ≤ q^t · L

### `averaging_list_lower_bound` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round11RSAveraging.averaging_list_lower_bound` [ArkLib/Data/CodingTheory/ProximityGap/AveragingListLowerBoundRS.lean:204](../../../ArkLib/Data/CodingTheory/ProximityGap/AveragingListLowerBoundRS.lean#L204) — **Main theorem — the averaging list LOWER bound as a genuine RS statement.** Fix a finite field `F`,
- `theorem RSDeltaStar.averaging_list_lower_bound` [ArkLib/Data/CodingTheory/ProximityGap/RSAveragingDeltaStarUpper.lean:203](../../../ArkLib/Data/CodingTheory/ProximityGap/RSAveragingDeltaStarUpper.lean#L203) — **Averaging list lower bound from an injection.** An injection from the size-`(k+t)` subsets into `l

### `averaging_pigeonhole` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round11RSAveraging.averaging_pigeonhole` [ArkLib/Data/CodingTheory/ProximityGap/AveragingListLowerBoundRS.lean:166](../../../ArkLib/Data/CodingTheory/ProximityGap/AveragingListLowerBoundRS.lean#L166) — Pigeonhole over the elementary-symmetric classes.  For ANY classifying map `cls` of the `a`-subsets
- `theorem RSDeltaStar.averaging_pigeonhole` [ArkLib/Data/CodingTheory/ProximityGap/RSAveragingDeltaStarUpper.lean:188](../../../ArkLib/Data/CodingTheory/ProximityGap/RSAveragingDeltaStarUpper.lean#L188) — **Averaging pigeonhole.** If `phi : alpha -> C x E` injects a finite family `S` whose first componen

### `badCount_udr_le` (2 declarations, 2 files)

- `theorem ProximityGap.UDRwire.badCount_udr_le` [ArkLib/Data/CodingTheory/ProximityGap/MCAUDRBound.lean:53](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAUDRBound.lean#L53) — (no docstring)
- `theorem ProximityGap.UDR.badCount_udr_le` [ArkLib/Data/CodingTheory/ProximityGap/UDRBadCount.lean:74](../../../ArkLib/Data/CodingTheory/ProximityGap/UDRBadCount.lean#L74) — (no docstring)

### `badGamma_le` (2 declarations, 2 files)

- `theorem ProximityGap.UDRwire.badGamma_le` [ArkLib/Data/CodingTheory/ProximityGap/MCAUDRBound.lean:35](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAUDRBound.lean#L35) — (no docstring)
- `theorem ProximityGap.UDR.badGamma_le` [ArkLib/Data/CodingTheory/ProximityGap/UDRBadCount.lean:56](../../../ArkLib/Data/CodingTheory/ProximityGap/UDRBadCount.lean#L56) — (no docstring)

### `badPolyAgreement` (2 declarations, 2 files)

- `def Issue29Ring.badPolyAgreement` [ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean:39](../../../ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean#L39) — **Named per-round residual = the weakened-KState bad event.** The prover message `p` differs from th
- `def KStateWeaken.badPolyAgreement` [ArkLib/ToMathlib/KStateWeaken.lean:70](../../../ArkLib/ToMathlib/KStateWeaken.lean#L70) — **Named per-round residual (weakened KState surface).** `badPolyAgreement r p q` is the bad event to

### `badStack` (2 declarations, 2 files)

- `def ProximityGap.MCAGSPrizeRefutation.badStack` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean:29](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean#L29) — The adversarial stack: row 0 = `w₀`, row 1 = `0`.
- `def badStack` [ArkLib/MCAGSRefutationCore.lean:28](../../../ArkLib/MCAGSRefutationCore.lean#L28) — The adversarial stack: row 0 = `w₀`, row 1 = `0`.

### `badStack_one` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.badStack_one` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean:32](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean#L32) — (no docstring)
- `theorem badStack_one` [ArkLib/MCAGSRefutationCore.lean:31](../../../ArkLib/MCAGSRefutationCore.lean#L31) — (no docstring)

### `badStack_zero` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.badStack_zero` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean:31](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean#L31) — (no docstring)
- `theorem badStack_zero` [ArkLib/MCAGSRefutationCore.lean:30](../../../ArkLib/MCAGSRefutationCore.lean#L30) — (no docstring)

### `badSumcheckEventProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.badSumcheckEventProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean:614](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean#L614) — (no docstring)
- `def RingSwitching.SumcheckPhase.badSumcheckEventProp` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:258](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L258) — **Named weakened-KState bad event for one ring-switching sumcheck round.** The prover's degree-`≤ 2`

### `batchingCoreRbrKnowledgeError` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:217](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L217) — Combined RBR knowledge error for batching + core interaction.
- `def RingSwitching.FullRingSwitching.batchingCoreRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/General.lean:190](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L190) — (no docstring)

### `batchingCoreReduction` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:95](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L95) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:69](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L69) — (no docstring)

### `batchingCoreVerifier` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:77](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L77) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:45](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L45) — (no docstring)

### `binTerm` (2 declarations, 2 files)

- `def CodingTheory.binTerm` [ArkLib/Data/CodingTheory/BinomialEntropyBound.lean:41](../../../ArkLib/Data/CodingTheory/BinomialEntropyBound.lean#L41) — The weighted binomial layer `C(n,i)·k^i·(n-k)^{n-i}`. As `i` ranges over `0..n` these are the layers
- `def ArkLib.ProximityGap.KKH26.binTerm` [ArkLib/Data/CodingTheory/ProximityGap/KKH26EntropyForm.lean:61](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26EntropyForm.lean#L61) — The `j`-th term of the binomial expansion of `(k + (n − k))^n` over `ℕ`.

### `binomial_separation` (2 declarations, 2 files)

- `theorem ProximityGap.MultiplicativeRigidity.binomial_separation` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean:154](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean#L154) — **Binomial separation.** If `0 < b < a ≤ k`, then two distinct monomials `c₁ * X ^ a` and `c₂ * X ^
- `theorem MultiplicativeRigidity.binomial_separation` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean:170](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean#L170) — **Binomial separation.** Packaging of coset rigidity in the form the dossier consumes: if `b < a < k

### `c0_ne_c1` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c0_ne_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:39](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L39) — The three codewords are pairwise distinct.
- `theorem JohnsonBound.JqlRefutation.c0_ne_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:79](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L79) — The three codewords are pairwise distinct.

### `c0_ne_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c0_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:40](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L40) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.c0_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:80](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L80) — (no docstring)

### `c1_ne_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c1_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:41](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L41) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.c1_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:81](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L81) — (no docstring)

### `c6_isRS` (2 declarations, 2 files)

- `lemma ArkLib.CodingTheory.TinyInteriorK3.c6_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:137](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L137) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.c6_isRS` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:148](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L148) — (no docstring)

### `capacitySegmentDup` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.capacitySegmentDup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:208](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L208) — The combined capacity segment collision event. This occurs if there is any capacity segment collisio
- `def OracleSpec.QueryLog.BadEventDSPaper.capacitySegmentDup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L184) — The combined capacity segment collision event. This occurs if there is any capacity segment collisio

### `capacitySegmentDupHash` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.capacitySegmentDupHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:151](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L151) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.capacitySegmentDupHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:127](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L127) — (no docstring)

### `capacitySegmentDupPerm` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.capacitySegmentDupPerm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:168](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L168) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.capacitySegmentDupPerm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:144](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L144) — (no docstring)

### `capacitySegmentDupPermInv` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.capacitySegmentDupPermInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:187](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L187) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.capacitySegmentDupPermInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:163](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L163) — (no docstring)

### `card` (2 declarations, 2 files)

- `theorem Probability.SizeSubset.card` [ArkLib/Data/Probability/Combinatorial.lean:47](../../../ArkLib/Data/Probability/Combinatorial.lean#L47) — The number of size-`n` subsets of a finite type is `\|α\| choose n`.
- `theorem Probability.SizedSubset.card` [ArkLib/Data/Probability/UniformSubset.lean:43](../../../ArkLib/Data/Probability/UniformSubset.lean#L43) — (no docstring)

### `card_allQueriesIn` (2 declarations, 2 files)

- `theorem Issue14Scratch.card_allQueriesIn` [ArkLib/ProofSystem/BatchedFri/QueryRoundAnalysis.lean:35](../../../ArkLib/ProofSystem/BatchedFri/QueryRoundAnalysis.lean#L35) — (= `Fri.QueryRound.card_allQueriesIn`) The number of length-`t` query tuples landing entirely in `G`
- `theorem Fri.QueryRound.card_allQueriesIn` [ArkLib/ProofSystem/BatchedFri/Security.lean:353](../../../ArkLib/ProofSystem/BatchedFri/Security.lean#L353) — The number of length-`t` query tuples landing entirely in a set `G` is `\|G\| ^ t`. This counts the ac

### `card_filter_eval_eq_le_natDegree` (2 declarations, 2 files)

- `theorem Issue29Ring.card_filter_eval_eq_le_natDegree` [ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean:52](../../../ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean#L52) — **Root-counting core (Schwartz–Zippel, finite-field form).** For two distinct polynomials, the set o
- `theorem KStateWeaken.card_filter_eval_eq_le_natDegree` [ArkLib/ToMathlib/KStateWeaken.lean:91](../../../ArkLib/ToMathlib/KStateWeaken.lean#L91) — **Root-counting core (CompPoly-free).** For two *distinct* polynomials, the set of challenges on whi

### `card_filter_forall_pi` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.card_filter_forall_pi` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:71](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L71) — Counting a coordinatewise event: the tuples satisfying `Q` in every coordinate form the `piFinset` o
- `theorem card_filter_forall_pi` [ArkLib/ToMathlib/CountingAgreementBricks.lean:76](../../../ArkLib/ToMathlib/CountingAgreementBricks.lean#L76) — Count of length-`s` tuples whose every coordinate satisfies `Q` equals `(#Q)^s`.

### `card_filter_ne_zero` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.BallVolume.card_filter_ne_zero` [ArkLib/Data/CodingTheory/ProximityGap/BallVolume.lean:33](../../../ArkLib/Data/CodingTheory/ProximityGap/BallVolume.lean#L33) — The number of nonzero field elements is `q - 1`.
- `theorem ArkLib.RandomLinearCode.card_filter_ne_zero` [ArkLib/Data/CodingTheory/RandomLinearCodeFirstMoment.lean:53](../../../ArkLib/Data/CodingTheory/RandomLinearCodeFirstMoment.lean#L53) — The number of nonzero messages is `qᵏ − 1`.

### `card_wordStack_eq` (2 declarations, 2 files)

- `theorem CS25.card_wordStack_eq` [ArkLib/Data/CodingTheory/ProximityGap/CS25JointProxBound.lean:255](../../../ArkLib/Data/CodingTheory/ProximityGap/CS25JointProxBound.lean#L255) — **`#stacks = Q^n`** for the interleaved alphabet `Q = \|κ→A\|`, `n = \|ι\|`.
- `theorem CodingTheory.card_wordStack_eq` [ArkLib/Data/CodingTheory/ProximityGap/CS25SecondMomentIsolation.lean:38](../../../ArkLib/Data/CodingTheory/ProximityGap/CS25SecondMomentIsolation.lean#L38) — The number of two-row stacks over `ι → F` equals `\|ι→F\|²`.

### `cert_natDegree_le` (2 declarations, 2 files)

- `theorem MuTwoPowDerandRefutation.cert_natDegree_le` [ArkLib/Data/CodingTheory/ProximityGap/MuTwoPowDerandRefutation.lean:166](../../../ArkLib/Data/CodingTheory/ProximityGap/MuTwoPowDerandRefutation.lean#L166) — (no docstring)
- `theorem ArkLib.XiCertReduction.cert_natDegree_le` [ArkLib/ToMathlib/XiCertReduction.lean:245](../../../ArkLib/ToMathlib/XiCertReduction.lean#L245) — The certificate degree bound for arbitrary `a : 𝒪 H`: the `Y`-degree of the canonical representative

### `charSum` (2 declarations, 2 files)

- `def ArkLib.CodingTheory.HasseWeilInstances.charSum` [ArkLib/Data/CodingTheory/ProximityGap/HasseWeilBoundInstances.lean:88](../../../ArkLib/Data/CodingTheory/ProximityGap/HasseWeilBoundInstances.lean#L88) — The complete quadratic character sum `∑ₓ χ(f x)`.
- `def ArkLib.ProximityGap.MomentCollisionSpectral.charSum` [ArkLib/Data/CodingTheory/ProximityGap/MomentCollisionSpectral.lean:66](../../../ArkLib/Data/CodingTheory/ProximityGap/MomentCollisionSpectral.lean#L66) — The Fourier coefficient `T ψ = ∑_S ψ (stat S)`.

### `choose_le_succ_succ` (2 declarations, 2 files)

- `theorem Round14ConstantGap.choose_le_succ_succ` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarConstantGapBelowCapacity.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarConstantGapBelowCapacity.lean#L51) — One-step Pascal: `C(n, m) ≤ C(n+1, m+1)` (the RHS is `C(n,m) + C(n,m+1)`).
- `theorem R15Bracket.choose_le_succ_succ` [ArkLib/Data/CodingTheory/ProximityGap/ScaleBracketFull.lean:278](../../../ArkLib/Data/CodingTheory/ProximityGap/ScaleBracketFull.lean#L278) — (no docstring)

### `choose_prime_pow_cast_eq_zero` (2 declarations, 2 files)

- `lemma ProximityGap.LinearizedPolynomialHasse.choose_prime_pow_cast_eq_zero` [ArkLib/Data/CodingTheory/ProximityGap/LinearizedPolynomialHasse.lean:70](../../../ArkLib/Data/CodingTheory/ProximityGap/LinearizedPolynomialHasse.lean#L70) — **Char-`p` middle binomial vanishing.** For a commutative ring of characteristic `p` (prime), `(p^a)
- `lemma ArkLib.ProximityGap.Issue232Bricks.choose_prime_pow_cast_eq_zero` [ArkLib/Data/CodingTheory/ProximityGap/VerifiedBricks.lean:73](../../../ArkLib/Data/CodingTheory/ProximityGap/VerifiedBricks.lean#L73) — **Char-`p` middle binomial vanishing.** In a commutative ring of prime characteristic `p`, `C(p^a, m

### `cliqueLocator_natDegree` (2 declarations, 2 files)

- `theorem Round19Clique.cliqueLocator_natDegree` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueBeachhead.lean:124](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueBeachhead.lean#L124) — The clique locator has `natDegree = \|W\| − 1` (product of `\|W\|−1` monic linears).
- `theorem Round20CliqueKernel.cliqueLocator_natDegree` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueKernelStructure.lean:84](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueKernelStructure.lean#L84) — Locator degree: `natDegree Λ_{E_α} = \|W\| − 1` for `α ∈ W`.

### `code` (2 declarations, 2 files)

- `def ArkLib.ProximityGap.Round3SubgroupSumsetDirect.code` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupSumsetThreePowUpper.lean:112](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupSumsetThreePowUpper.lean#L112) — The `{−1,0,1}` coefficient code of a full-domain subset `S ⊆ Fin (N+N)` at low index `j`, as an elem
- `def ReedSolomon.code` [ArkLib/Data/CodingTheory/ReedSolomon.lean:62](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L62) — The Reed-Solomon code for polynomials of degree less than `deg` and evaluation points `domain`.

### `coefAt` (2 declarations, 2 files)

- `def Round25General.coefAt` [ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean:85](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityGeneralT1.lean#L85) — The coefficient profile of one point.
- `def Round24Triples.coefAt` [ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean:59](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityTriplesSunflower.lean#L59) — The single-point integer coefficient profile.

### `coeffHom` (2 declarations, 2 files)

- `def ProximityPrize.BCIKS20.GammaGenuine.coeffHom` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/GammaGenuine.lean:87](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/GammaGenuine.lean#L87) — The per-`Y`-coefficient ring hom `F[X][Y] → (𝕃 H)⟦X⟧`: recenter the `X`-layer at `x₀` (`taylorAlgHom
- `def ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:175](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L175) — Reading off the `k`-th coefficient of the underlying polynomial, as an additive homomorphism `Rq Φ →

### `coeff_S_eq_zero_of_lt` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_eq_zero_of_lt` [ArkLib/Data/Polynomial/HenselExistence.lean:203](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L203) — The `t`-th partial sum is supported on `[0, t]`: every coefficient above order `t` vanishes. (`S t`
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_eq_zero_of_lt` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:280](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L280) — `S t` is supported on `[0, t]`: every coefficient above order `t` vanishes.

### `coeff_S_stable` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_stable` [ArkLib/Data/Polynomial/HenselExistence.lean:214](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L214) — Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`. The diagonal value is reached a
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_stable` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:290](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L290) — Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`.

### `coeff_S_succ_of_le` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_succ_of_le` [ArkLib/Data/Polynomial/HenselExistence.lean:197](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L197) — Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_succ_of_le` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:275](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L275) — Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.

### `coeff_aeval_eq_sum_range` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_aeval_eq_sum_range` [ArkLib/Data/Polynomial/HenselExistence.lean:65](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L65) — Local copy of `NewtonLinearization.coeff_aeval_eq_sum_range`: `coeff n (aeval γ P) = ∑_{i ≤ deg P} P
- `theorem ProximityPrize.NewtonLinearization.coeff_aeval_eq_sum_range` [ArkLib/Data/Polynomial/NewtonLinearization.lean:166](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L166) — Local restatement of the `HasSubst`-free `aeval`-coefficient expansion (this is `ProximityPrize.coef

### `coeff_aeval_sub_at` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_aeval_sub_at` [ArkLib/Data/Polynomial/HenselExistence.lean:147](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L147) — Local copy of `NewtonLinearization.coeff_aeval_sub_at` (the `P'(c)`-linear response). For `P : R[X]`
- `theorem ProximityPrize.NewtonLinearization.coeff_aeval_sub_at` [ArkLib/Data/Polynomial/NewtonLinearization.lean:186](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L186) — **Newton/Hensel linearization of the composed series (P2 form).** For a polynomial `P` over `R` and

### `coeff_pow_natDegree_le` (2 declarations, 2 files)

- `lemma CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.coeff_pow_natDegree_le` [ArkLib/Data/CodingTheory/ProximityGap/Hab25Production.lean:396](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25Production.lean#L396) — Coefficient `Z`-degree bound for powers: if every coefficient of `p ∈ F[Z][X]` has `Z`-degree `≤ m`,
- `lemma ArkLib.SurfaceFactorProduction.coeff_pow_natDegree_le` [ArkLib/ToMathlib/SurfaceFactorProduction.lean:90](../../../ArkLib/ToMathlib/SurfaceFactorProduction.lean#L90) — (no docstring)

### `coeff_toPoly` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.CyclotomicModulus.coeff_toPoly` [ArkLib/Data/Lattices/CyclotomicRing/Galois/Automorphism.lean:124](../../../ArkLib/Data/Lattices/CyclotomicRing/Galois/Automorphism.lean#L124) — **(S3)** Coefficient bridge: the Mathlib and `CPolynomial` coefficients agree.
- `lemma UniPoly.coeff_toPoly` [ArkLib/Data/UniPoly/Basic.lean:785](../../../ArkLib/Data/UniPoly/Basic.lean#L785) — characterize `p.toPoly` by showing that its coefficients are exactly the coefficients of `p`

### `coeff_γ` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_γ` [ArkLib/Data/Polynomial/HenselExistence.lean:227](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L227) — (no docstring)
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_γ` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:303](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L303) — (no docstring)

### `coeff_γ_eq_S` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_γ_eq_S` [ArkLib/Data/Polynomial/HenselExistence.lean:236](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L236) — `γ` agrees with the `t`-th partial sum below order `t + 1`.
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_γ_eq_S` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:312](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L312) — `γ` agrees with the `t`-th partial sum below order `t + 1`.

### `coeffs` (2 declarations, 2 files)

- `def Polynomial.Bivariate.coeffs` [ArkLib/Data/Polynomial/Bivariate.lean:34](../../../ArkLib/Data/Polynomial/Bivariate.lean#L34) — The set of coefficients of a bivariate polynomial.
- `def UniPoly.coeffs` [ArkLib/Data/UniPoly/Basic.lean:41](../../../ArkLib/Data/UniPoly/Basic.lean#L41) — (no docstring)

### `collision` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Collision.collision` [ArkLib/Data/CodingTheory/ProximityGap/CollisionLemma.lean:40](../../../ArkLib/Data/CodingTheory/ProximityGap/CollisionLemma.lean#L40) — **Collision lemma.** If `P` is `r`-close to `u₀+γ·u₁` and `P'` is `r`-close to `u₀+γ'·u₁` with `γ ≠
- `def ArkLib.ProximityGap.MomentCollisionSpectral.collision` [ArkLib/Data/CodingTheory/ProximityGap/MomentCollisionSpectral.lean:62](../../../ArkLib/Data/CodingTheory/ProximityGap/MomentCollisionSpectral.lean#L62) — Statistic-collision count for an arbitrary finite-abelian-group-valued statistic.

### `collisionBwdBwd` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.collisionBwdBwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L263) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.collisionBwdBwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:239](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L239) — (no docstring)

### `collisionBwdFwd` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.collisionBwdFwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:281](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L281) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.collisionBwdFwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:257](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L257) — (no docstring)

### `collisionFwdBwd` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.collisionFwdBwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:272](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L272) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.collisionFwdBwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L248) — (no docstring)

### `collisionFwdFwd` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.collisionFwdFwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:254](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L254) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.collisionFwdFwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:230](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L230) — (no docstring)

### `collisionPerm` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.collisionPerm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:290](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L290) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.collisionPerm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:266](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L266) — (no docstring)

### `combined` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.combined` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:225](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L225) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.combined` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:201](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L201) — (no docstring)

### `computeRoundPoly` (2 declarations, 2 files)

- `def Sumcheck.Structured.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured.lean:130](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L130) — The general round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` is the public multilinea
- `def Sumcheck.Structured.Prismalinear.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:70](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L70) — The *prismalinear* round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` has per-variable

### `constCode` (2 declarations, 2 files)

- `def ProximityGap.MCANearCapacity.constCode` [ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityLowerBound.lean:59](../../../ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityLowerBound.lean#L59) — The length-`n` constant (repetition) Reed–Solomon code `RS[ZMod p, ·, 1]`: the degree-`<1` polynomia
- `def ProximityGap.MCAWitnessSpread.Example.constCode` [ArkLib/Data/CodingTheory/ProximityGap/MCAWitnessSpreadExample.lean:46](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAWitnessSpreadExample.lean#L46) — The constant-functions (repetition) code over `ZMod 3` on three coordinates. It is the rate-`1/3` Re

### `constantCoeff_eval` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselSeriesCoeff.constantCoeff_eval` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:252](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L252) — `constantCoeff (eval γ Q) = eval (constantCoeff γ) Q₀`: the order-0 part of the evaluated series is
- `theorem ArkLib.PerPlaceSep.constantCoeff_eval` [ArkLib/ToMathlib/PerPlaceSeparabilitySupply.lean:99](../../../ArkLib/ToMathlib/PerPlaceSeparabilitySupply.lean#L99) — The residue map commutes with polynomial evaluation: `π (f.eval a) = (f.map π).eval (π a)`.

### `constantCoeff_γ` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.constantCoeff_γ` [ArkLib/Data/Polynomial/HenselExistence.lean:231](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L231) — The constant coefficient of the Newton root is the prescribed root `c`.
- `theorem ProximityPrize.HenselSeriesCoeff.constantCoeff_γ` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:307](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L307) — The constant coefficient of the Newton root is the prescribed root `c`.

### `constraintMapCurve_eq_mulVec` (2 declarations, 2 files)

- `theorem GuruswamiSudan.OverRatFunc.ZDegree.constraintMapCurve_eq_mulVec` [ArkLib/Data/CodingTheory/GuruswamiSudan/GSCurveInterpolantZDegree.lean:95](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GSCurveInterpolantZDegree.lean#L95) — The matrix `gsMatrixZCurve`, mapped into `K = F(Z)`, represents `constraintMap` for the curve fold o
- `theorem GuruswamiSudan.OverRatFunc.ZDegree.Curve.constraintMapCurve_eq_mulVec` [ArkLib/Data/CodingTheory/GuruswamiSudan/GSInterpolantZDegreeCurve.lean:101](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GSInterpolantZDegreeCurve.lean#L101) — The matrix `gsMatrixZCurve`, mapped into `K = F(Z)`, represents `constraintMap` for the `L`-ary curv

### `coord` (2 declarations, 2 files)

- `def CodingTheory.ExtensionFieldPresentation.coord` [ArkLib/Data/CodingTheory/ExtensionCodes.lean:100](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean#L100) — The `j`-th coordinate `φᵢ : F →ₗ[B] B` of an extension-field presentation, as a `B`-linear map.
- `def MuTwoPowDerandRefutation.coord` [ArkLib/Data/CodingTheory/ProximityGap/MuTwoPowDerandRIMRank.lean:49](../../../ArkLib/Data/CodingTheory/ProximityGap/MuTwoPowDerandRIMRank.lean#L49) — The coordinate (in `Fin 8`) of the edge represented by each row of `rimMatrix`.

### `coreInteractionOracleRbrKnowledgeError` (2 declarations, 2 files)

- `def coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1158](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1158) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1728](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1728) — (no docstring)

### `coreInteractionOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1129](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1129) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1688](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1688) — Perfect completeness for the core interaction oracle reduction

### `coreInteractionOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1166](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1166) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1737](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1737) — Round-by-round knowledge soundness for the core interaction oracle verifier

### `correlatedAgreement_affine_curves_of_lattice_data` (2 declarations, 2 files)

- `theorem ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_data` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean:885](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean#L885) — [BCIKS20] Theorem 1.5 consuming concrete square-lattice data. This is the data-level counterpart of
- `theorem ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_of_lattice_data` [ArkLib/ToMathlib/BoundaryDischarge.lean:542](../../../ArkLib/ToMathlib/BoundaryDischarge.lean#L542) — The affine-curves keystone can consume the exact lattice branch through the smaller `BoundaryCardLat

### `correlatedAgreement_affine_curves_of_lattice_data_isSquare` (2 declarations, 2 files)

- `theorem ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_data_isSquare` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean:1002](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean#L1002) — Curve-facing square-endpoint adapter from concrete lattice data. This is the data-level counterpart
- `theorem ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_of_lattice_data_isSquare` [ArkLib/ToMathlib/BoundaryDischarge.lean:605](../../../ArkLib/ToMathlib/BoundaryDischarge.lean#L605) — Curve-facing square-endpoint adapter from `BoundaryCardLatticeData`.  This is the lattice-data count

### `coset` (2 declarations, 2 files)

- `def ArkLib.ProximityGap.CosetConcentration.coset` [ArkLib/Data/CodingTheory/ProximityGap/CosetPowerSumConcentration.lean:92](../../../ArkLib/Data/CodingTheory/ProximityGap/CosetPowerSumConcentration.lean#L92) — The coset `g · ⟨ζ⟩` as a finset (image of `range h` under `l ↦ g·ζ^l`).
- `def ArkLib.ProximityGap.HybridDepthNoGo.coset` [ArkLib/Data/CodingTheory/ProximityGap/HybridConcentrationDepthNoGo.lean:99](../../../ArkLib/Data/CodingTheory/ProximityGap/HybridConcentrationDepthNoGo.lean#L99) — The deep coset as a finset; for a primitive `h`-th root and `g ≠ 0` it has exactly `h` elements and

### `coset_finset_powersum_zero` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.CosetConcentration.coset_finset_powersum_zero` [ArkLib/Data/CodingTheory/ProximityGap/CosetPowerSumConcentration.lean:104](../../../ArkLib/Data/CodingTheory/ProximityGap/CosetPowerSumConcentration.lean#L104) — Power sum of degree `i` (`1 ≤ i < h`) over a single coset finset is `0`.
- `theorem ArkLib.ProximityGap.HybridDepthNoGo.coset_finset_powersum_zero` [ArkLib/Data/CodingTheory/ProximityGap/HybridConcentrationDepthNoGo.lean:109](../../../ArkLib/Data/CodingTheory/ProximityGap/HybridConcentrationDepthNoGo.lean#L109) — (no docstring)

### `coset_powersum_zero` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.CosetConcentration.coset_powersum_zero` [ArkLib/Data/CodingTheory/ProximityGap/CosetPowerSumConcentration.lean:74](../../../ArkLib/Data/CodingTheory/ProximityGap/CosetPowerSumConcentration.lean#L74) — **Coset power-sum vanishing (load-bearing).** `ζ ^ h = 1`, `ζ ^ i ≠ 1` ⟹ the `i`-th power sum over t
- `theorem ArkLib.ProximityGap.HybridDepthNoGo.coset_powersum_zero` [ArkLib/Data/CodingTheory/ProximityGap/HybridConcentrationDepthNoGo.lean:80](../../../ArkLib/Data/CodingTheory/ProximityGap/HybridConcentrationDepthNoGo.lean#L80) — **Coset power-sum vanishing (the deep atom).** `ζ^h = 1`, `ζ^i ≠ 1` ⟹ the `i`-th power sum over the

### `coset_powersum_zero_of_lt` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.CosetConcentration.coset_powersum_zero_of_lt` [ArkLib/Data/CodingTheory/ProximityGap/CosetPowerSumConcentration.lean:84](../../../ArkLib/Data/CodingTheory/ProximityGap/CosetPowerSumConcentration.lean#L84) — **All low power-sums vanish on a coset.** Primitive `h`-th root `ζ`, `1 ≤ i < h`.
- `theorem ArkLib.ProximityGap.HybridDepthNoGo.coset_powersum_zero_of_lt` [ArkLib/Data/CodingTheory/ProximityGap/HybridConcentrationDepthNoGo.lean:90](../../../ArkLib/Data/CodingTheory/ProximityGap/HybridConcentrationDepthNoGo.lean#L90) — A coset of a primitive `h`-th root kills the first `h−1` power sums.

### `curveCaptured_improve` (2 declarations, 2 files)

- `theorem CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.curveCaptured_improve` [ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCapture.lean:168](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCapture.lean#L168) — **The `L`-ary improvement lemma** (mirrors `affineCaptured_improve`): capture with codeword-degree r
- `theorem MutualCorrAgreement.curveCaptured_improve` [ArkLib/ProofSystem/Whir/MCAConjectureEllaryReduction.lean:191](../../../ArkLib/ProofSystem/Whir/MCAConjectureEllaryReduction.lean#L191) — **The ℓ-ary improvement lemma** (Hab25 "from the proof of Lemma 1", curve form). If `γ` is curve-cap

### `curveDecodable_of_marked` (2 declarations, 2 files)

- `theorem ProximityGap.CurveDec.curveDecodable_of_marked` [ArkLib/Data/CodingTheory/ProximityGap/CurveDecodability.lean:130](../../../ArkLib/Data/CodingTheory/ProximityGap/CurveDecodability.lean#L130) — **Marked ⟹ original ([Jo26] Theorem 5.5, easy half).**  Any `a`-subset of the close set is a valid m
- `theorem ProximityGap.curveDecodable_of_marked` [ArkLib/Data/CodingTheory/ProximityGap/GG25MarkedCurve.lean:70](../../../ArkLib/Data/CodingTheory/ProximityGap/GG25MarkedCurve.lean#L70) — **Theorem 5.5, (marked → original).** The marked property at any `a`-subset of the close set yields

### `curveGap` (2 declarations, 2 files)

- `def CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.curveGap` [ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCapture.lean:56](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCapture.lean#L56) — The `L`-ary gap functional `∑ⱼ zʲ·dⱼ(x)`.
- `def MutualCorrAgreement.curveGap` [ArkLib/ProofSystem/Whir/MCAConjectureEllaryReduction.lean:86](../../../ArkLib/ProofSystem/Whir/MCAConjectureEllaryReduction.lean#L86) — The ℓ-ary gap functional at one coordinate: `γ ↦ ∑ⱼ γʲ·cⱼ` — the `L`-ary generalization of the affin

### `curve_endgame_count` (2 declarations, 2 files)

- `theorem CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.curve_endgame_count` [ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCapture.lean:104](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCapture.lean#L104) — **The `L`-ary endgame count.** Any set of scalars, each a root of the gap functional at some disagre
- `theorem MutualCorrAgreement.curve_endgame_count` [ArkLib/ProofSystem/Whir/MCAConjectureEllaryReduction.lean:143](../../../ArkLib/ProofSystem/Whir/MCAConjectureEllaryReduction.lean#L143) — **Hab25 Claim-1 endgame, ℓ-ary.** If every scalar of `T` matches the fold at some coordinate of the

### `decidablePred_badPolyAgreement` (2 declarations, 2 files)

- `instance Issue29Ring.decidablePred_badPolyAgreement` [ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean:42](../../../ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean#L42) — (no docstring)
- `instance KStateWeaken.decidablePred_badPolyAgreement` [ArkLib/ToMathlib/KStateWeaken.lean:74](../../../ArkLib/ToMathlib/KStateWeaken.lean#L74) — (no docstring)

### `decodeMessagePhiInv` (3 declarations, 2 files)

- `lemma DuplexSpongeFS.Hyb23Bricks.decodeMessagePhiInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:116](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L116) — `φ_j⁻¹` (brute-force preimage search) succeeds iff a serialize-preimage exists.
- `lemma DuplexSpongeFS.Hyb23Bricks.decodeMessagePhiInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:126](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L126) — A `φ_j⁻¹` witness re-serializes to the input block (the `List.find?` success property).
- `def DuplexSpongeFS.TraceTransform.decodeMessagePhiInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean:115](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean#L115) — Implements the deterministic inverse codec map `φ_i⁻¹ : Im(φ_i) → ℳ_{P,i}`. Because `φ_i` (via `inst

### `decoder` (2 declarations, 2 files)

- `def BerlekampWelch.decoder` [ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:52](../../../ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean#L52) — Berlekamp-Welch decoder for Reed-Solomon codes. Given received codeword evaluations with potential e
- `def GuruswamiSudan.decoder` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:113](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L113) — Specification-level Guruswami-Sudan decoder. This finite-field specification enumerates all degree-`

### `degree` (2 declarations, 2 files)

- `def UniPoly.degree` [ArkLib/Data/UniPoly/Basic.lean:66](../../../ArkLib/Data/UniPoly/Basic.lean#L66) — Return the degree of a `UniPoly`.
- `def StirIOP.degree` [ArkLib/ProofSystem/Stir/MainThm.lean:45](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L45) — **Degree after `i` folds:** The starting degree is `deg`; every fold divides it by `foldingParamⱼ (j

### `disagree_card_le` (2 declarations, 2 files)

- `theorem CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.Hab25JohnsonDichotomyData.disagree_card_le` [ArkLib/Data/CodingTheory/ProximityGap/Hab25JohnsonDichotomy.lean:98](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25JohnsonDichotomy.lean#L98) — **The dichotomy counting theorem (proven).**  Every factor contributes at most `max T n` exceptional
- `theorem ArkLib.CodingTheory.WindowedFoldingTransfer.disagree_card_le` [ArkLib/Data/CodingTheory/ProximityGap/WindowedFoldingTransfer.lean:38](../../../ArkLib/Data/CodingTheory/ProximityGap/WindowedFoldingTransfer.lean#L38) — Agreement `≥ t` bounds the disagreement count by `n − t`.

### `dist` (2 declarations, 2 files)

- `def Code.dist` [ArkLib/Data/CodingTheory/Basic/Distance.lean:216](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean#L216) — The Hamming distance of a code `C` is the minimum Hamming distance between any two distinct elements
- `def dist` [ArkLib/Data/CodingTheory/Quarantine/Hypotheses.lean:21](../../../ArkLib/Data/CodingTheory/Quarantine/Hypotheses.lean#L21) — (no docstring)

### `domain_implies_char_ne_2` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:98](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L98) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:134](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L134) — (no docstring)

### `duplexSpongeTraceEntry` (2 declarations, 2 files)

- `abbrev OracleSpec.duplexSpongeTraceEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:371](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L371) — The type of a single entry in a duplex sponge query trace. Implicit-parameter companion to `DSTraceS
- `abbrev DuplexSpongeFS.DSTraceStorage.duplexSpongeTraceEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean:48](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean#L48) — A single query-answer entry of a `DuplexSpongeTrace`, i.e. one element of the underlying `QueryLog`

### `empty` (2 declarations, 2 files)

- `def DuplexSpongeFS.DSTraceStorage.ListBacked.empty` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean:530](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean#L530) — (no docstring)
- `def ProtocolSpec.empty` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:55](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L55) — The empty protocol specification, with no messages or challenges, written as `!p[]`.

### `encode` (2 declarations, 2 files)

- `def ProximityGap.KKH26ExactCensus.encode` [ArkLib/Data/CodingTheory/ProximityGap/KKH26ExactCensusCharZero.lean:125](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26ExactCensusCharZero.lean#L125) — The encoder: a class set `A ⊆ range 2^{k−1}` and a positive-sign subset `B ⊆ A` produce the antipoda
- `def ReedSolomon.encode` [ArkLib/Data/CodingTheory/ReedSolomon.lean:123](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L123) — (no docstring)

### `energy_H16` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257.energy_H16` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat257.lean:71](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat257.lean#L71) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537.energy_H16` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat65537.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat65537.lean#L63) — **Order-16 energy is `720 ≤ 768 = 3\|G\|²`** — anti-concentration HOLDS here, whereas at `q = 257` the

### `energy_H8` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat257.energy_H8` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat257.lean:70](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat257.lean#L70) — (no docstring)
- `theorem ArkLib.ProximityGap.SubgroupAdditiveEnergyFermat65537.energy_H8` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat65537.lean:58](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupAdditiveEnergyFermat65537.lean#L58) — **Order-8 energy is the `q`-independent char-0 value `168`** — identical to `F₂₅₇`, confirming minim

### `epsCA_ge_one_sub_inv_of_allButOne` (2 declarations, 2 files)

- `theorem CodingTheory.Bridge.AllButOne.epsCA_ge_one_sub_inv_of_allButOne` [ArkLib/ToMathlib/BGKS20AllButOne.lean:102](../../../ArkLib/ToMathlib/BGKS20AllButOne.lean#L102) — **T5.4 endpoint from the "all but one scalar" producer.** Under the hypotheses of `nearCertainBadLin
- `theorem CodingTheory.Bridge.epsCA_ge_one_sub_inv_of_allButOne` [ArkLib/ToMathlib/NearCertainBadLineProof.lean:103](../../../ArkLib/ToMathlib/NearCertainBadLineProof.lean#L103) — **T5.4 endpoint from an all-but-one near-certain bad line.**

### `epsCA_le_one` (2 declarations, 2 files)

- `theorem ProximityGap.epsCA_le_one` [ArkLib/Data/CodingTheory/ProximityGap/Errors.lean:247](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean#L247) — The CA error is bounded by the total probability mass.
- `theorem CodingTheory.Bridge.epsCA_le_one` [ArkLib/ToMathlib/BridgeListDecodingCA.lean:65](../../../ArkLib/ToMathlib/BridgeListDecodingCA.lean#L65) — **`ε_ca ≤ 1`.** The correlated-agreement error is a supremum of values each of which is either `0` o

### `epsMCA_le_card_div_at_granularity` (2 declarations, 2 files)

- `theorem ProximityGap.MCAAntichainEngine.epsMCA_le_card_div_at_granularity` [ArkLib/Data/CodingTheory/ProximityGap/MCAAntichainEngine.lean:179](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAAntichainEngine.lean#L179) — **The tight granularity cap:** `ε_mca(C, 1/n) ≤ n/q` for every linear code.
- `theorem ProximityGap.MCAWitnessCountEngine.epsMCA_le_card_div_at_granularity` [ArkLib/Data/CodingTheory/ProximityGap/MCAWitnessCountEngine.lean:208](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAWitnessCountEngine.lean#L208) — **Sharper granularity cap:** the universal witness in the raw `n + 1` witness-family count does not

### `epsMCAgs_badList_eq_one` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.epsMCAgs_badList_eq_one` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean:82](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean#L82) — **`epsMCAgs = 1` for the adversarial list family.** This is the refutation kernel: a non-faithful `L
- `theorem epsMCAgs_badList_eq_one` [ArkLib/MCAGSRefutationCore.lean:81](../../../ArkLib/MCAGSRefutationCore.lean#L81) — **`epsMCAgs = 1` for the adversarial list family.** This is the refutation kernel: a non-faithful `L

### `epsRbr` (2 declarations, 2 files)

- `def Core2Keystone.epsRbr` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:72](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L72) — The WHIR per-challenge RBR error (verbatim from `Whir/RbrBudgetAccounting.lean:74`).
- `def Issue113WHIR.epsRbr` [ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean:74](../../../ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean#L74) — The WHIR per-challenge RBR error: the maximum over the budget set. Mirror of `whir_rbr_soundness`'s

### `epsRbr_le_of_forall_le` (2 declarations, 2 files)

- `theorem Core2Keystone.epsRbr_le_of_forall_le` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:278](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L278) — **§3.2 — antitone transport to a dominating budget (the keystone budget is tight).** The `epsRbr` bu
- `theorem Issue113WHIR.epsRbr_le_of_forall_le` [ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean:158](../../../ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean#L158) — **Tightness / universal property: `ε_rbr` is the SMALLEST uniform per-challenge bound.** If a candid

### `eqPoly_evalC_eq_C_eval` (2 declarations, 2 files)

- `theorem Spartan.Spec.eqPoly_evalC_eq_C_eval` [ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean:41](../../../ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean#L41) — (no docstring)
- `theorem Spartan.eqPoly_evalC_eq_C_eval` [ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean:31](../../../ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean#L31) — Fixing the `eqPolynomial` row variables at `r_x` via `C` commutes with `C` of the base-ring evaluati

### `esymm_one_eq_sum` (2 declarations, 2 files)

- `theorem ProximityGap.CensusLowerBound.esymm_one_eq_sum` [ArkLib/Data/CodingTheory/ProximityGap/CensusLowerBound.lean:82](../../../ArkLib/Data/CodingTheory/ProximityGap/CensusLowerBound.lean#L82) — The first elementary symmetric function of a multiset is its sum.
- `lemma ProximityGap.esymm_one_eq_sum` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumRadiusOne.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumRadiusOne.lean#L63) — The first elementary symmetric function of a multiset is its sum.

### `eval` (2 declarations, 2 files)

- `def UniPoly.eval` [ArkLib/Data/UniPoly/Basic.lean:412](../../../ArkLib/Data/UniPoly/Basic.lean#L412) — Evaluates a `UniPoly` at a given value
- `def Plonk.Gate.eval` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:54](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L54) — Evaluate a gate on a given input vector.

### `evalDist_cast_uniformSample` (2 declarations, 2 files)

- `theorem Prover.evalDist_cast_uniformSample` [ArkLib/OracleReduction/Composition/Sequential/ChallengeSeamBridge.lean:74](../../../ArkLib/OracleReduction/Composition/Sequential/ChallengeSeamBridge.lean#L74) — **Atom 2: uniform sampling is invariant under transport along a type equality.** For `h : A = B` wit
- `theorem OptionTStateT.evalDist_cast_uniformSample` [ArkLib/OracleReduction/RunUnroll.lean:369](../../../ArkLib/OracleReduction/RunUnroll.lean#L369) — **Transport of uniform sampling along a type equality.** If `α = β` (propositionally), the uniform s

### `evalOnPoints_injOn_degreeLT` (2 declarations, 2 files)

- `theorem ArkLib.CS25.evalOnPoints_injOn_degreeLT` [ArkLib/Data/CodingTheory/ProximityGap/CS25RSEncodingInjective.lean:28](../../../ArkLib/Data/CodingTheory/ProximityGap/CS25RSEncodingInjective.lean#L28) — **Reed–Solomon encoding injectivity.**  For `k ≤ n`, `evalOnPoints` is injective on degree-`<k` poly
- `theorem ReedSolomon.evalOnPoints_injOn_degreeLT` [ArkLib/Data/CodingTheory/ProximityGap/ReedSolomonUniqueDecode.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/ReedSolomonUniqueDecode.lean#L63) — **Reed–Solomon evaluation injectivity.**  A degree-`< k` polynomial is determined by its Reed–Solomo

### `evalX_myR` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.evalX_myR` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:82](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L82) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.evalX_myR` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:87](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L87) — `evalX (C 0) R = H = 2·Y`.

### `even_psum_halves` (2 declarations, 2 files)

- `theorem Round28FullWindow.even_psum_halves` [ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean:98](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean#L98) — **The even power sums halve:** for antipodally-closed `A`, `p_{2l}(A) = 2 · p_l(A²)` — summing `x^{2
- `theorem Round26Recursion.even_psum_halves` [ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean:96](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean#L96) — **The even power sums halve:** for antipodally-closed `A`, `p_{2l}(A) = 2 · p_l(A²)` — summing `x^{2

### `exists_challenge_flip_of_full` (2 declarations, 2 files)

- `theorem Verifier.KnowledgeStateFunction.exists_challenge_flip_of_full` [ArkLib/OracleReduction/Security/RbrKnowledgeFlip.lean:61](../../../ArkLib/OracleReduction/Security/RbrKnowledgeFlip.lean#L61) — **First-crossing for knowledge state functions, in the rbr-game event shape.** If the input statemen
- `theorem Verifier.StateFunction.exists_challenge_flip_of_full` [ArkLib/OracleReduction/Security/RoundByRound.lean:521](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L521) — **State-function first-crossing on the realized transcript.**  Specialization of `exists_challenge_f

### `exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` (2 declarations, 2 files)

- `lemma ProximityGap.exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6727](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6727) — Complement-to-incidence form of the heavy-coordinate argument.  If a coordinate is not heavy for the
- `lemma ArkLib.Claim511.exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` [ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean:129](../../../ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean#L129) — **Complement-to-incidence selection.** If at least `r` coordinates are *not* heavy (each bad for `<

### `exists_monic_irreducible_factorization` (2 declarations, 2 files)

- `theorem Polynomial.exists_monic_irreducible_factorization` [ArkLib/ToMathlib/MonicIrreducibleFactorization.lean:29](../../../ArkLib/ToMathlib/MonicIrreducibleFactorization.lean#L29) — Every monic polynomial of positive degree over a domain is a product of monic irreducible factors.
- `theorem ArkLib.PigeonholeFactorSupply.exists_monic_irreducible_factorization` [ArkLib/ToMathlib/PigeonholeFactorSupply.lean:168](../../../ArkLib/ToMathlib/PigeonholeFactorSupply.lean#L168) — **The monic irreducible factorization** over a UFD coefficient ring.

### `exists_ne_zero_map_eq_zero` (2 declarations, 2 files)

- `theorem GSMultInterp.exists_ne_zero_map_eq_zero` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:215](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L215) — **Abstract underdetermined-system existence** (mirrors `BCKHS25.exists_ne_zero_map_eq_zero`): a line
- `theorem BCKHS25.exists_ne_zero_map_eq_zero` [ArkLib/Data/CodingTheory/ProximityGap/BCKHS25/Interpolation.lean:71](../../../ArkLib/Data/CodingTheory/ProximityGap/BCKHS25/Interpolation.lean#L71) — Abstract underdetermined-system existence: a linear map between finite-dimensional spaces with stric

### `exists_subset_card_eq_of_le_card` (2 declarations, 2 files)

- `lemma ProximityGap.exists_subset_card_eq_of_le_card` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6677](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6677) — Select exactly `r` elements from a finite set once its cardinality is large enough.  This is the fin
- `lemma ArkLib.Claim511.exists_subset_card_eq_of_le_card` [ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean:119](../../../ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean#L119) — Select exactly `r` elements from a finite set once its cardinality is large enough.  Final selection

### `exp_root_primitive` (2 declarations, 2 files)

- `lemma DeBruijnTowerWiring.exp_root_primitive` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnTowerWiring.lean:294](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnTowerWiring.lean#L294) — (no docstring)
- `lemma TwoPrimeWindowLaw.exp_root_primitive` [ArkLib/Data/CodingTheory/ProximityGap/TwoPrimeWindowLaw.lean:550](../../../ArkLib/Data/CodingTheory/ProximityGap/TwoPrimeWindowLaw.lean#L550) — (no docstring)

### `exp_three_primitive` (2 declarations, 2 files)

- `lemma DeBruijnThreePrimeIntGrid.exp_three_primitive` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnThreePrimeIntGrid.lean:523](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnThreePrimeIntGrid.lean#L523) — (no docstring)
- `lemma DeBruijnWeightedSquarefree.exp_three_primitive` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedSquarefree.lean:219](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedSquarefree.lean#L219) — (no docstring)

### `exp_two_primitive` (2 declarations, 2 files)

- `lemma DeBruijnThreePrimeIntGrid.exp_two_primitive` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnThreePrimeIntGrid.lean:519](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnThreePrimeIntGrid.lean#L519) — (no docstring)
- `lemma DeBruijnWeightedSquarefree.exp_two_primitive` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedSquarefree.lean:215](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedSquarefree.lean#L215) — (no docstring)

### `extractability` (2 declarations, 2 files)

- `def Commitment.extractability` [ArkLib/CommitmentScheme/Basic.lean:242](../../../ArkLib/CommitmentScheme/Basic.lean#L242) — A commitment scheme satisfies **extractability** with error `extractabilityError` if there exists a
- `def CommitmentScheme.extractability` [ArkLib/CommitmentScheme/CommitmentScheme.lean:159](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L159) — A commitment scheme satisfies **extractability** with error `extractabilityError` if there exists a

### `extractor` (2 declarations, 2 files)

- `def CheckClaim.extractor` [ArkLib/ProofSystem/Component/CheckClaim.lean:167](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L167) — The round-by-round extractor for the `CheckClaim` reduction. Trivial since the witness is `Unit`.
- `def ReduceClaim.extractor` [ArkLib/ProofSystem/Component/ReduceClaim.lean:166](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L166) — The round-by-round extractor for the `ReduceClaim` (oracle) reduction. Requires a mapping `mapWitInv

### `fact_prime_eleven` (2 declarations, 2 files)

- `instance ArkLib.CodingTheory.TinyInteriorF11.fact_prime_eleven` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11.lean:58](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11.lean#L58) — `11` is prime, so `ZMod 11` is a field, making `RS[F₁₁, F₁₁, 2]` a genuine Reed–Solomon code.
- `instance ArkLib.CodingTheory.TinyInteriorK3.fact_prime_eleven` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:81](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L81) — `11` is prime, so `ZMod 11` is a field. This is what makes `RS[F₁₁, F₁₁, 3]` a genuine Reed–Solomon

### `failureProbability` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.failureProbability` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:132](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L132) — Paper-facing alias for CO25 Definition 3.7 failure probability.
- `def Verifier.failureProbability` [ArkLib/OracleReduction/Security/Rewinding.lean:163](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L163) — CO25 Definition 3.7, adapted to ArkLib's non-interactive verifier interface. The paper's size bound

### `failureProbabilityFamily` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.failureProbabilityFamily` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:142](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L142) — Paper-facing alias for CO25 Definition 3.7 with explicit security parameter `λ`.
- `def Verifier.failureProbabilityFamily` [ArkLib/OracleReduction/Security/Rewinding.lean:249](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L249) — CO25 Definition 3.7 with the security parameter `λ` made explicit as an external index.

### `fiatShamir_completeness_of_runEq` (2 declarations, 2 files)

- `theorem Reduction.fiatShamir_completeness_of_runEq` [ArkLib/OracleReduction/FiatShamir/Basic.lean:424](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L424) — Basic Fiat-Shamir completeness follows from the named run-equality residual and completeness of the
- `theorem Issue116.fiatShamir_completeness_of_runEq` [ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean:79](../../../ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean#L79) — Forward direction packaged for downstream users: basic FS completeness from the run-equality residua

### `fiatShamir_completeness_unroll_of_runEq` (2 declarations, 2 files)

- `theorem Reduction.fiatShamir_completeness_unroll_of_runEq` [ArkLib/OracleReduction/FiatShamir/Basic.lean:387](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L387) — The named run-equality residual is enough to unroll basic-Fiat-Shamir completeness to the explicit h
- `theorem Issue116.fiatShamir_completeness_unroll_of_runEq` [ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean:65](../../../ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean#L65) — Completeness of the transformed one-message basic Fiat-Shamir reduction is equivalent to the explici

### `fiberCount` (2 declarations, 2 files)

- `def AveragingCrossover.fiberCount` [ArkLib/Data/CodingTheory/ProximityGap/AveragingFiberConservation.lean:85](../../../ArkLib/Data/CodingTheory/ProximityGap/AveragingFiberConservation.lean#L85) — The fiber count over a target.
- `def Round18Bracket.fiberCount` [ArkLib/Data/CodingTheory/ProximityGap/TwoSidedBracketScale.lean:47](../../../ArkLib/Data/CodingTheory/ProximityGap/TwoSidedBracketScale.lean#L47) — The fiber count `m x = #{c : x ∈ A c}`.

### `fiber_card_le` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.SmoothFiberCount.fiber_card_le` [ArkLib/Data/CodingTheory/ProximityGap/SmoothFiberCount.lean:30](../../../ArkLib/Data/CodingTheory/ProximityGap/SmoothFiberCount.lean#L30) — Any fiber of the `m`-power map inside a set of field elements has at most `m` points (`m ≥ 1`): they
- `lemma TwoGenPackingCapacity.fiber_card_le` [ArkLib/Data/CodingTheory/ProximityGap/TwoGenPackingCapacity.lean:181](../../../ArkLib/Data/CodingTheory/ProximityGap/TwoGenPackingCapacity.lean#L181) — Bases below `s` in a fixed residue class mod `G` (`G ∣ s`) number at most `s / G`.

### `fiber_scaling` (2 declarations, 2 files)

- `theorem ClassChart.fiber_scaling` [ArkLib/Data/CodingTheory/ProximityGap/ClassChartBounds.lean:93](../../../ArkLib/Data/CodingTheory/ProximityGap/ClassChartBounds.lean#L93) — Pointwise weighted scaling of power sums: `p_j(λ·S) = λ^j · p_j(S)`. Copied verbatim (with provenanc
- `theorem LamLeungTwoPow.fiber_scaling` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean:520](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean#L520) — **The weighted-scaling orbit**: multiplication by a unit `λ` carries the `(ē₁, …)`-power-sum fiber b

### `finSumFinEquiv_symm_dite` (2 declarations, 2 files)

- `theorem RingSwitching.finSumFinEquiv_symm_dite` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1638](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1638) — Value-form of `finSumFinEquiv.symm`: classify the index by whether its value is `< m`.
- `theorem finSumFinEquiv_symm_dite` [ArkLib/ToMathlib/FinSumMvPolyBricks.lean:25](../../../ArkLib/ToMathlib/FinSumMvPolyBricks.lean#L25) — Value-form classification of `finSumFinEquiv.symm`.

### `finalSumcheckKStateProp` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1359](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1359) — (no docstring)
- `def RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1536](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1536) — (no docstring)

### `finalSumcheckKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:206](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L206) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1309](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1309) — RBR knowledge error for the final sumcheck step

### `finalSumcheckKnowledgeStateFunction` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1399](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1399) — The knowledge state function for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1573](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1573) — The knowledge state function for the final sumcheck step

### `finalSumcheckOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1620](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1620) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1706](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1706) — Round-by-round knowledge soundness for the final sumcheck step

### `finalSumcheckRbrExtractor` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1320](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1320) — The round-by-round extractor for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1516](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1516) — The round-by-round extractor for the final sumcheck step

### `finalSumcheckStepLogic` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1098](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1098) — The Logic Instance for the final sumcheck step. This is a 1-message protocol where the prover sends
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:577](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L577) — The logic instance for the FRI final sumcheck step.

### `finalSumcheckStep_is_logic_complete` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_is_logic_complete` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1697](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1697) — **The final sumcheck step logic is strongly complete** (direct proof; discharges the former `FinalSu
- `lemma Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_is_logic_complete` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1076](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1076) — Strong completeness of the FRI final sumcheck logic step.

### `finalSumcheckStep_verifierCheck_passed` (3 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1252](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1252) — The final sumcheck verifier check follows directly from sumcheck consistency and witness structure.
- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1546](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1546) — The verifier check passes in the final sumcheck step. **Proof structure:** 1. From `sumcheckConsiste
- `lemma Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:991](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L991) — Verifier check passes in the FRI final sumcheck logic step.

### `firstOracleWitnessConsistency_unique` (2 declarations, 2 files)

- `lemma Binius.BBFSmallFieldIOPCS.firstOracleWitnessConsistency_unique` [ArkLib/ProofSystem/Binius/BBFSmallFieldIOPCS.lean:180](../../../ArkLib/ProofSystem/Binius/BBFSmallFieldIOPCS.lean#L180) — Uniqueness of the polynomial witness from first-oracle UDR-compatibility.
- `lemma Binius.BinaryBasefold.CoreInteraction.firstOracleWitnessConsistency_unique` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean:763](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean#L763) — (no docstring)

### `firstSumcheckWithTarget_toVerifier_isFailingDet` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.firstSumcheckWithTarget_toVerifier_isFailingDet` [ArkLib/ProofSystem/Spartan/ComposedTightRbrKnowledge.lean:317](../../../ArkLib/ProofSystem/Spartan/ComposedTightRbrKnowledge.lean#L317) — **`hV₃` witness for the tight fold: the target-preserving first sum-check verifier is failing-determ
- `theorem Spartan.Spec.firstSumcheckWithTarget_toVerifier_isFailingDet` [ArkLib/ProofSystem/Spartan/TightDeterminismWitnesses.lean:35](../../../ArkLib/ProofSystem/Spartan/TightDeterminismWitnesses.lean#L35) — **`hV₃` witness (tight chain): the carried first sum-check verifier is failing-deterministic.**

### `floor_lt_of_lt_of_lattice` (2 declarations, 2 files)

- `theorem ArkLib.Issue64Boundary.floor_lt_of_lt_of_lattice` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardLatticeSlice.lean:93](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardLatticeSlice.lean#L93) — **At a lattice point, every strict sub-radius drops the floor.**  If `δ·n` is an integer (`(⌊δ·n⌋ :
- `theorem ArkLib.BoundaryCardResidual.floor_lt_of_lt_of_lattice` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean:172](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean#L172) — **At a lattice endpoint, every strict sub-radius has strictly smaller floor.**  This is the exact co

### `foldAt` (2 declarations, 2 files)

- `def ProximityGap.Issue357.FoldQuotientStack.foldAt` [ArkLib/Data/CodingTheory/ProximityGap/KKH26FoldQuotientStack.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26FoldQuotientStack.lean#L51) — The FRI fold of `f` at challenge `β`, evaluated at the fiber `{x, −x}` (the value assigned to `y = x
- `def ProximityGap.KKH26FoldTransport.foldAt` [ArkLib/Data/CodingTheory/ProximityGap/KKH26FoldTransport.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26FoldTransport.lean#L63) — The FRI fold of a word `f`, evaluated at the point lying over `y = x²`: the even part plus `β` times

### `foldMatrixNat_det_ne_zero` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.foldMatrixNat_det_ne_zero` [ArkLib/ProofSystem/Binius/BinaryBasefold/FoldDetDischarge.lean:124](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/FoldDetDischarge.lean#L124) — **Issue #317: every fold matrix in the `≤ ℓ` range is nonsingular.**
- `theorem Binius.BinaryBasefold.DetNeZero.foldMatrixNat_det_ne_zero` [ArkLib/ProofSystem/Binius/BinaryBasefold/FoldDetSplit.lean:288](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/FoldDetSplit.lean#L288) — **The induction** (issue #317): every `foldMatrixNat` within the `≤ ℓ` range has nonzero determinant

### `foldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.foldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean:163](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean#L163) — (no docstring)
- `theorem WhirIOP.FoldRound.foldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Whir/FoldRound.lean:265](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L265) — **Perfect completeness of the honest WHIR fold round.** The honest prover folds its committed codewo

### `foldProver` (2 declarations, 2 files)

- `def Fri.Spec.FoldPhase.foldProver` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:400](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L400) — The prover for the `i`-th round of the FRI protocol. It first receives the challenge, then does an `
- `def WhirIOP.FoldRound.foldProver` [ArkLib/ProofSystem/Whir/FoldRound.lean:174](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L174) — The honest fold-round prover. It receives `α`, folds its committed function, and sends the folded or

### `foldVal` (2 declarations, 2 files)

- `def LamLeungTwoPow.foldVal` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean:479](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean#L479) — The folded error values: sums of `v` over squaring fibers.
- `def ArkLib.IteratedFold.foldVal` [ArkLib/ToMathlib/IteratedFoldConservation.lean:50](../../../ArkLib/ToMathlib/IteratedFoldConservation.lean#L50) — The even folded error values: sums of `v` over squaring fibers.

### `foldValOdd` (2 declarations, 2 files)

- `def LamLeungTwoPow.foldValOdd` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean:543](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean#L543) — The odd-fold values: `∑_{x²=y} v(x)·x`.
- `def ArkLib.IteratedFold.foldValOdd` [ArkLib/ToMathlib/IteratedFoldConservation.lean:54](../../../ArkLib/ToMathlib/IteratedFoldConservation.lean#L54) — The odd folded error values: sums of `v x · x` over squaring fibers.

### `foldValOdd_polyeval` (2 declarations, 2 files)

- `theorem LamLeungTwoPow.foldValOdd_polyeval` [ArkLib/Data/CodingTheory/ProximityGap/FoldPolynomialSlices.lean:155](../../../ArkLib/Data/CodingTheory/ProximityGap/FoldPolynomialSlices.lean#L155) — **The odd fold of a polynomial error is the odd coefficient slice, twisted by `y`.**
- `theorem ArkLib.IteratedSliceCoherence.foldValOdd_polyeval` [ArkLib/Data/CodingTheory/ProximityGap/IteratedSliceRootCoherence.lean:160](../../../ArkLib/Data/CodingTheory/ProximityGap/IteratedSliceRootCoherence.lean#L160) — The odd fold of a polynomial error is `X ·` the odd coefficient slice.

### `foldVal_polyeval` (2 declarations, 2 files)

- `theorem LamLeungTwoPow.foldVal_polyeval` [ArkLib/Data/CodingTheory/ProximityGap/FoldPolynomialSlices.lean:142](../../../ArkLib/Data/CodingTheory/ProximityGap/FoldPolynomialSlices.lean#L142) — **The even fold of a polynomial error is the even coefficient slice.**
- `theorem ArkLib.IteratedSliceCoherence.foldVal_polyeval` [ArkLib/Data/CodingTheory/ProximityGap/IteratedSliceRootCoherence.lean:153](../../../ArkLib/Data/CodingTheory/ProximityGap/IteratedSliceRootCoherence.lean#L153) — The even fold of a polynomial error is the even coefficient slice (the `FoldPolynomialSlices` law, r

### `foldVerifier` (2 declarations, 2 files)

- `def Fri.Spec.FoldPhase.foldVerifier` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:454](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L454) — The oracle verifier for the `i`-th non-final folding round of the FRI protocol.
- `def WhirIOP.FoldRound.foldVerifier` [ArkLib/ProofSystem/Whir/FoldRound.lean:192](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L192) — The honest fold-round verifier. It performs no consistency check (that is deferred to the query phas

### `fold_mass_conservation` (2 declarations, 2 files)

- `theorem LamLeungTwoPow.fold_mass_conservation` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean:625](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean#L625) — **Fold-mass conservation at a fiber**: both folds vanishing at `y` forces the error to vanish on the
- `theorem ArkLib.IteratedFold.fold_mass_conservation` [ArkLib/ToMathlib/IteratedFoldConservation.lean:104](../../../ArkLib/ToMathlib/IteratedFoldConservation.lean#L104) — **Fold-mass conservation at a fiber** (the 1-level law, self-contained): both folds vanishing at `y`

### `four_pow_le_shift_choose` (2 declarations, 2 files)

- `theorem Round14ConstantGap.four_pow_le_shift_choose` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarConstantGapBelowCapacity.lean:68](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarConstantGapBelowCapacity.lean#L68) — **Rate-1/2 engine.** For `t < m`: `4^{m−t} ≤ 2(m−t) · C(2m, m+t)`. Chain: `C(2m, m+t) ≥ C(2(m−t), m−
- `theorem R15Bracket.four_pow_le_shift_choose` [ArkLib/Data/CodingTheory/ProximityGap/ScaleBracketFull.lean:292](../../../ArkLib/Data/CodingTheory/ProximityGap/ScaleBracketFull.lean#L292) — Central-binomial lower bound after a Pascal shift by `2t`: `4^(m−t) ≤ 2(m−t) · C(2m, m+t)` for `t <

### `fullOracleVerifier_rbrKnowledgeSoundness_wired` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness_wired` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:255](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L255) — **Round-by-round knowledge soundness of the full Binary Basefold oracle verifier, wired** (stateless
- `theorem RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness_wired` [ArkLib/ProofSystem/RingSwitching/RbrKnowledgeWiringFull.lean:119](../../../ArkLib/ProofSystem/RingSwitching/RbrKnowledgeWiringFull.lean#L119) — **Round-by-round knowledge soundness of the full ring-switching oracle verifier, wired** — no append

### `fullPspec` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.fullPspec` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:54](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L54) — (no docstring)
- `def RingSwitching.fullPspec` [ArkLib/ProofSystem/RingSwitching/Spec.lean:57](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L57) — (no docstring)

### `gapPoly` (2 declarations, 2 files)

- `def CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.gapPoly` [ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCapture.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCapture.lean#L60) — The per-coordinate gap polynomial `∑ⱼ C(dⱼ(x))·Xʲ`.
- `def ArkLib.ProximityGap.KKH26.gapPoly` [ArkLib/Data/CodingTheory/ProximityGap/KKH26GapCensusLaw.lean:48](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26GapCensusLaw.lean#L48) — The line-minus-explanation polynomial `X^A + λ·X^B − q`.

### `genMutualCorrParamsUDR` (2 declarations, 2 files)

- `def Fold.genMutualCorrParamsUDR` [ArkLib/ProofSystem/Whir/FoldingGenMutualCorrParamsUDR.lean:63](../../../ArkLib/ProofSystem/Whir/FoldingGenMutualCorrParamsUDR.lean#L63) — **The unique-decoding-window instance of `Fold.GenMutualCorrParams`.** Given the per-level power-dom
- `def WhirIOP.genMutualCorrParamsUDR` [ArkLib/ProofSystem/Whir/GenMutualCorrParamsUDR.lean:148](../../../ArkLib/ProofSystem/Whir/GenMutualCorrParamsUDR.lean#L148) — **The unique-decoding-window instance of `GenMutualCorrParams`.** Given the per-round power-domain d

### `getBit_eq_testBit` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.QueryPhase.getBit_eq_testBit` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:302](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L302) — (no docstring)
- `lemma Binius.BinaryBasefold.getBit_eq_testBit` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Lift.lean:41](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Lift.lean#L41) — (no docstring)

### `getSumcheckRoundPoly_eval_eq_sum_snoc` (2 declarations, 2 files)

- `theorem RingSwitching.SumcheckPhase.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:297](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L297) — **Target (b): `getSumcheckRoundPoly` value as a cube sum (LAST-variable/`snoc` form, defect-#20 repa
- `theorem Sumcheck.Structured.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:117](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L117) — **Round-univariate evaluation as a survivor-cube sum (last-variable / `snoc` form).** Evaluating the

### `gsMatrixZCurve` (2 declarations, 2 files)

- `def GuruswamiSudan.OverRatFunc.ZDegree.gsMatrixZCurve` [ArkLib/Data/CodingTheory/GuruswamiSudan/GSCurveInterpolantZDegree.lean:58](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GSCurveInterpolantZDegree.lean#L58) — The `L`-ary curve-fold Guruswami–Sudan constraint system as a matrix over `F[Z]` (the inner `F[X]` i
- `def GuruswamiSudan.OverRatFunc.ZDegree.Curve.gsMatrixZCurve` [ArkLib/Data/CodingTheory/GuruswamiSudan/GSInterpolantZDegreeCurve.lean:68](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GSInterpolantZDegreeCurve.lean#L68) — The `L`-ary curve-fold Guruswami–Sudan constraint system as a matrix over `F[Z]` (the inner `F[X]` i

### `gs_list_size_bound` (2 declarations, 2 files)

- `theorem GSListSizeBound.gs_list_size_bound` [ArkLib/Data/CodingTheory/GuruswamiSudan/ListSizeBound.lean:130](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/ListSizeBound.lean#L130) — **Guruswami–Sudan list-size bound.** Let `Q : F[X][Y]` be a nonzero interpolant of `(1, k-1)`-weight
- `theorem CodingTheory.Bounds.gs_list_size_bound` [ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean:91](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds/GuruswamiSudanListSize.lean#L91) — **Guruswami–Sudan list-size bound.** If `Q ≠ 0` has `Y`-degree `≤ deg_Y`, then the set of candidate

### `guruswami_sudan_for_proximity_gap_existence` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:758](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L758) — Constructive witness extraction for the Guruswami–Sudan system. When the computable `hasWitnessC` ch
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:201](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L201) — The first part of Lemma 5.3 from [BCIKS20]. Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`pr

### `guruswami_sudan_for_proximity_gap_property` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:797](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L797) — Constructive witness property for the Guruswami–Sudan system. When `m > 0` and the codeword polynomi
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:213](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L213) — The second part of Lemma 5.3 from [BCIKS20]. For any solution `Q` of the Guruswami-Sudan system, and

### `h30_agreement_lower_bound` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.PromotedHypotheses.h30_agreement_lower_bound` [ArkLib/Data/CodingTheory/ProximityGap/PromotedHypotheses.lean:40](../../../ArkLib/Data/CodingTheory/ProximityGap/PromotedHypotheses.lean#L40) — (no docstring)
- `theorem h30_agreement_lower_bound` [ArkLib/Data/CodingTheory/ProximityGap/PromotedHypothesesC.lean:11](../../../ArkLib/Data/CodingTheory/ProximityGap/PromotedHypothesesC.lean#L11) — H30: Any vector must agree with some codeword on `k` coordinates. Since we can interpolate on any se

### `ham_c0_c1` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c0_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:44](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L44) — Pairwise Hamming distances.
- `theorem JohnsonBound.JqlRefutation.ham_c0_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:84](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L84) — Pairwise Hamming distances.

### `ham_c0_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c0_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:45](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L45) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.ham_c0_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:85](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L85) — (no docstring)

### `ham_c1_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c1_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:46](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L46) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.ham_c1_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:86](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L86) — (no docstring)

### `hammingDist_add_right` (2 declarations, 2 files)

- `theorem GHSZ02RS.hammingDist_add_right` [ArkLib/Data/CodingTheory/ListDecoding/GHSZ02Foundations.lean:91](../../../ArkLib/Data/CodingTheory/ListDecoding/GHSZ02Foundations.lean#L91) — Hamming distance is translation-invariant on the right.
- `lemma ArkLib.CodingTheory.ListMoments.hammingDist_add_right` [ArkLib/Data/CodingTheory/ProximityGap/ListSizeMoments.lean:41](../../../ArkLib/Data/CodingTheory/ProximityGap/ListSizeMoments.lean#L41) — **Hamming distance is translation invariant**: adding the same `v` to both arguments leaves the dist

### `hammingDist_comp_equiv` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.hammingDist_comp_equiv` [ArkLib/ProofSystem/Binius/BinaryBasefold/ExtractMLPCorrectness.lean:69](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ExtractMLPCorrectness.lean#L69) — Hamming distance is invariant under precomposition with an equivalence of the index type.
- `lemma BKR06.hammingDist_comp_equiv` [ArkLib/ToMathlib/BKR06EndToEnd.lean:524](../../../ArkLib/ToMathlib/BKR06EndToEnd.lean#L524) — Index relabeling preserves the Hamming distance.  (Mathlib's `hammingDist_comp` is codomain-side com

### `hammingDist_sub_right` (2 declarations, 2 files)

- `theorem Round13bSecondMoment.hammingDist_sub_right` [ArkLib/Data/CodingTheory/ProximityGap/BallIntersectionSecondMomentLinear.lean:36](../../../ArkLib/Data/CodingTheory/ProximityGap/BallIntersectionSecondMomentLinear.lean#L36) — **Translation invariance of Hamming distance:** `Δ(x−z, y−z) = Δ(x, y)`, via `hammingDist_comp` with
- `theorem ArkLib.CS25.hammingDist_sub_right` [ArkLib/Data/CodingTheory/ProximityGap/CS25SecondMomentReduction.lean:35](../../../ArkLib/Data/CodingTheory/ProximityGap/CS25SecondMomentReduction.lean#L35) — Hamming distance is translation invariant: `Δ₀(w, c) = Δ₀(w - c, 0)`.

### `hasseCoeff` (2 declarations, 2 files)

- `def GSMultInterp.hasseCoeff` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:136](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L136) — The order-`(a, b)` *Hasse coefficient* of the bivariate polynomial `Q = ∑_{(s,t)∈monoIdx} c(s,t)·X^s
- `def ArkLib.GS.hasseCoeff` [ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean:67](../../../ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean#L67) — The bivariate Hasse–Taylor coefficient of bidegree `(i, j)` of `Q` at `(a, b)`: take the `j`-th oute

### `hasseDerivX` (2 declarations, 2 files)

- `def BCIKS20.HenselNumerator.hasseDerivX` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:478](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L478) — `Δ_X^{i1}`: the `i1`-th Hasse derivative on the **lift `X` layer** (the middle `Polynomial` layer) o
- `def Polynomial.Bivariate.hasseDerivX` [ArkLib/Data/CodingTheory/ProximityGap/BruteForce.lean:54](../../../ArkLib/Data/CodingTheory/ProximityGap/BruteForce.lean#L54) — `Δ_X^{k}`: the `k`-th Hasse derivative in the inner variable `X`, applied coefficient-wise: each `Y`

### `hasseDerivX_monomial` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.hasseDerivX_monomial` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:47](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L47) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.hasseDerivX_monomial` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:54](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L54) — `Δ_X` on a single `Y`-monomial.

### `hasseDerivY` (2 declarations, 2 files)

- `def BCIKS20.HenselNumerator.hasseDerivY` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:483](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L483) — `Δ_Y^{m}`: the `m`-th Hasse derivative on the **outermost `Y` layer** of `R`, i.e. the ordinary math
- `def Polynomial.Bivariate.hasseDerivY` [ArkLib/Data/CodingTheory/ProximityGap/BruteForce.lean:49](../../../ArkLib/Data/CodingTheory/ProximityGap/BruteForce.lean#L49) — `Δ_Y^{k}`: the `k`-th Hasse derivative in the outer variable `Y`, i.e. the ordinary mathlib `Polynom

### `hasseDeriv_X_pow_prime_pow_sub_one` (2 declarations, 2 files)

- `theorem ProximityGap.LinearizedPolynomialHasse.hasseDeriv_X_pow_prime_pow_sub_one` [ArkLib/Data/CodingTheory/ProximityGap/LinearizedPolynomialHasse.lean:92](../../../ArkLib/Data/CodingTheory/ProximityGap/LinearizedPolynomialHasse.lean#L92) — **Inseparable vanishing-polynomial form.** In characteristic `p`, `hasseDeriv m (X^{p^a} - 1) = 0` f
- `theorem ArkLib.ProximityGap.Issue232Bricks.hasseDeriv_X_pow_prime_pow_sub_one` [ArkLib/Data/CodingTheory/ProximityGap/VerifiedBricks.lean:87](../../../ArkLib/Data/CodingTheory/ProximityGap/VerifiedBricks.lean#L87) — **Hasse–Lucas collapse of the vanishing polynomial.** Over a characteristic-`p` ring, `hasseDeriv m

### `hasseDeriv_eval_eq_sum` (2 declarations, 2 files)

- `theorem Issue9Hensel.hasseDeriv_eval_eq_sum` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HasseEvalConnectives.lean:29](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HasseEvalConnectives.lean#L29) — (no docstring)
- `theorem Polynomial.hasseDeriv_eval_eq_sum` [ArkLib/ToMathlib/Polynomial/HasseDerivEval.lean:36](../../../ArkLib/ToMathlib/Polynomial/HasseDerivEval.lean#L36) — **Hasse-derivative evaluation identity (★).** The evaluation of the order-`k` Hasse derivative of `p

### `heavyCoords_card_mul_le` (2 declarations, 2 files)

- `lemma ProximityGap.heavyCoords_card_mul_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6685](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6685) — Generic double-counting brick for Claim 5.11. If each `z ∈ S` has at most `m` bad coordinates, then
- `lemma ArkLib.Claim511.heavyCoords_card_mul_le` [ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean:78](../../../ArkLib/ToMathlib/BCIKS20CorrelatedAgreement.lean#L78) — **Double-counting brick.** If each `z ∈ S` has at most `m` bad coordinates, then the coordinates tha

### `hint` (2 declarations, 2 files)

- `def DomainSeparator.hint` [ArkLib/Data/Hash/DomainSep.lean:230](../../../ArkLib/Data/Hash/DomainSep.lean#L230) — Hint `count` native elements. Rust interface: ```rust pub fn hint(self, label: &str) -> Self ```
- `def HashStateWithInstructions.hint` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:192](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L192) — Process a hint operation. Rust interface: ```rust pub fn hint(&mut self) -> Result<(), DomainSeparat

### `hybEncodedMessagesBefore` (6 declarations, 2 files)

- `lemma DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:224](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L224) — `hybEncodedMessagesBefore?` is the walk applied to the flattened prefix.
- `lemma DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:302](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L302) — **H23-2.** `hybEncodedMessagesBefore?` succeeds whenever every encoded block before the round lies i
- `lemma DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:343](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L343) — **H23-2 glue.** On any backtrack output passing the simulator's image guard, the `Hyb₃` codec bridge
- `lemma DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:418](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L418) — **H23-3.** On success of `hybEncodedMessagesBefore?`, every decoded message re-serializes to the cor
- `lemma DuplexSpongeFS.Hyb23Bricks.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:432](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L432) — **H23-4.** Two encoded prefixes decoding (via `hybEncodedMessagesBefore?`) to the same message prefi
- `def DuplexSpongeFS.TraceTransform.hybEncodedMessagesBefore` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean:368](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean#L368) — Public wrapper for the Section 5.8 `φ⁻¹` parser from the encoded-message tuple returned by `BackTrac

### `id_isHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_isHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:332](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L332) — The zero-round identity oracle reduction is HVZK for any oracle-input relation.
- `theorem Reduction.id_isHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:375](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L375) — The zero-round identity reduction is honest-verifier zero-knowledge for any relation.

### `id_isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_isStatHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:342](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L342) — The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and any e
- `theorem Reduction.id_isStatHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:384](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L384) — The zero-round identity reduction is statistically honest-verifier zero-knowledge for any relation a

### `id_perfectHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_perfectHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:304](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L304) — The zero-round identity oracle reduction is perfect HVZK for any oracle-input relation.
- `theorem Reduction.id_perfectHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:355](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L355) — The zero-round identity reduction satisfies perfect honest-verifier zero-knowledge for any input rel

### `id_statisticalHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_statisticalHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:318](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L318) — The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and any e
- `theorem Reduction.id_statisticalHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:366](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L366) — The zero-round identity reduction satisfies statistical honest-verifier zero-knowledge for any relat

### `idxToSigma_inl` (2 declarations, 2 files)

- `theorem ArkLib.SeqComposeRbrKnowledge.idxToSigma_inl` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:69](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L69) — `seqComposeChallengeIdxToSigma` along the `inl` embedding of a head challenge index lands in the fir
- `theorem ArkLib.SeqComposeRbrSoundness.idxToSigma_inl` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:91](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L91) — `seqComposeChallengeIdxToSigma` along the `inl` embedding of a head challenge index lands in the fir

### `idxToSigma_inr` (2 declarations, 2 files)

- `theorem ArkLib.SeqComposeRbrKnowledge.idxToSigma_inr` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:96](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L96) — `seqComposeChallengeIdxToSigma` along the `inr` embedding of a tail challenge index: the first compo
- `theorem ArkLib.SeqComposeRbrSoundness.idxToSigma_inr` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:118](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L118) — `seqComposeChallengeIdxToSigma` along the `inr` embedding of a tail challenge index: the first compo

### `inflate` (2 declarations, 2 files)

- `def ArkLib.ProximityGap.Round4PairingRecursion.inflate` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPairingInflate.lean:166](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPairingInflate.lean#L166) — The inflated subset built from a base `B` and a set `P` of (untouched) pairs to double: `B ∪ doubled
- `def ArkLib.ProximityGap.Round4ZeroSumInflation.inflate` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumZeroInflation.lean:86](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumZeroInflation.lean#L86) — The inflation map: glue a base window `S₀` onto the union of a chosen collection `T` of zero-sum pai

### `injOn` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injOn` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:233](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L233) — (no docstring)
- `lemma Domain.FftDomain.injOn` [ArkLib/Data/Domain/FftDomain/Defs.lean:116](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L116) — (no docstring)

### `injective` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injective` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:228](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L228) — (no docstring)
- `lemma Domain.FftDomain.injective` [ArkLib/Data/Domain/FftDomain/Defs.lean:112](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L112) — (no docstring)

### `inputAns` (2 declarations, 2 files)

- `def StirIOP.MultiRound.inputAns` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:180](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L180) — The honest answer of the input-codeword oracle (ascribed at `F`).
- `def Whir302Checked.inputAns` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:132](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L132) — The honest answer of the public input oracle.

### `instChalFintype` (2 declarations, 2 files)

- `instance Whir302.instChalFintype` [ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean:37](../../../ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean#L37) — (no docstring)
- `instance Whir302RBR.instChalFintype` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:396](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L396) — (no docstring)

### `instChalInhabited` (2 declarations, 2 files)

- `instance Whir302.instChalInhabited` [ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean:45](../../../ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean#L45) — (no docstring)
- `instance Whir302RBR.instChalInhabited` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:404](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L404) — (no docstring)

### `instFactDeg` (2 declarations, 2 files)

- `instance BCIKS20.HenselNumerator.WeightWitness.instFactDeg` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:77](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L77) — (no docstring)
- `instance BCIKS20.HenselNumerator.Witness.instFactDeg` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:84](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L84) — (no docstring)

### `instFactIrr` (2 declarations, 2 files)

- `instance BCIKS20.HenselNumerator.WeightWitness.instFactIrr` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:76](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L76) — (no docstring)
- `instance BCIKS20.HenselNumerator.Witness.instFactIrr` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:83](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L83) — (no docstring)

### `int_thread_vanishing_of_vanishing` (2 declarations, 2 files)

- `lemma DeBruijnIntRelations.int_thread_vanishing_of_vanishing` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntRelations.lean:592](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntRelations.lean#L592) — The ℤ-coefficient non-coprime thread split (the O93/O101 split for ℤ weights, by the shift trick fro
- `theorem IntegerThreadSplit.int_thread_vanishing_of_vanishing` [ArkLib/Data/CodingTheory/ProximityGap/IntegerThreadSplit.lean:88](../../../ArkLib/Data/CodingTheory/ProximityGap/IntegerThreadSplit.lean#L88) — **ℤ THREAD-SPLIT, forward** (the O93/O101 engine with ℤ-multiplicities): for a prime `p` with `p² ∣

### `interior_list_two_sided` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round3SmoothF17.interior_list_two_sided` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:239](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L239) — **Two-sided interior list-size pin for the smooth-domain code `RS[F₁₇, ⟨2⟩, 2]` at `δ = 5/8`.** Ther
- `theorem ArkLib.CodingTheory.TinyInteriorTwoSided.interior_list_two_sided` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorTwoSidedF7.lean:197](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorTwoSidedF7.lean#L197) — **Two-sided interior list-size pin for `RS[F₇, F₇, 2]` at `δ = 4/7`.** There exists a received word

### `interior_radius_concrete_t2` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round5SliceRankT2.interior_radius_concrete_t2` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorT2TwoSymmetric.lean:370](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorT2TwoSymmetric.lean#L370) — **The `t = 2` interior hypothesis is non-vacuous (concrete instance).** At `k = 50`, `n = 220`: `(k+
- `theorem ArkLib.CodingTheory.Round6Stepanov.interior_radius_concrete_t2` [ArkLib/Data/CodingTheory/ProximityGap/StepanovPointCountEngine.lean:248](../../../ArkLib/Data/CodingTheory/ProximityGap/StepanovPointCountEngine.lean#L248) — **The joint-count containment is non-vacuous.** For `t = 2` the agreement size `a = k+2` is the genu

### `interpolate` (2 declarations, 2 files)

- `def ReedSolomon.interpolate` [ArkLib/Data/CodingTheory/ReedSolomon.lean:631](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L631) — The linear map that maps a codeword `f : ι → F` to a degree < \|ι\| polynomial p, such that `p(x) = f(
- `def UniPoly.Lagrange.interpolate` [ArkLib/Data/UniPoly/Basic.lean:1120](../../../ArkLib/Data/UniPoly/Basic.lean#L1120) — This function produces the polynomial which is of degree n and is equal to r i at ω^i for i = 0, 1,

### `isHVZK` (2 declarations, 2 files)

- `def OracleReduction.isHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:62](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L62) — Existential perfect HVZK for an oracle reduction.
- `def Reduction.isHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:90](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L90) — A reduction is honest-verifier zero-knowledge for relation `rel` if some simulator achieves perfect

### `isHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:397](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L397) — **OracleReduction `isHVZK` transfers along an equal honest distribution.**
- `theorem Reduction.isHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:480](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L480) — **`isHVZK` transfers along an `evalDist`-equal honest distribution.**

### `isHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:424](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L424) — **OracleReduction `isHVZK` honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.isHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:506](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L506) — **`isHVZK` honest-distribution congruence with opposite-order equality.**

### `isHVZK.isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.isStatHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:151](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L151) — Perfect HVZK existence for oracle reductions implies statistical HVZK existence.
- `theorem Reduction.isHVZK.isStatHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:198](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L198) — **Perfect HVZK implies statistical HVZK existence** at any error.

### `isHVZK.isStatHVZK_mono_relation_error` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.isStatHVZK_mono_relation_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:275](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L275) — Perfect HVZK existence for oracle reductions transports to statistical HVZK on a restricted relation
- `theorem Reduction.isHVZK.isStatHVZK_mono_relation_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:305](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L305) — **Perfect HVZK existence gives statistical HVZK on any subrelation and relaxed error.**

### `isHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:118](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L118) — `isHVZK` for oracle reductions is antitone in the relation.
- `theorem Reduction.isHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:167](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L167) — **`isHVZK` is antitone in the relation.** HVZK for `rel` implies HVZK for any `rel' ⊆ rel` (the same

### `isHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:523](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L523) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for exact HVZK at
- `theorem Reduction.isHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:597](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L597) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for exact HVZK.**

### `isHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:509](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L509) — **Existential zero-error approximate honest-distribution transfer for exact HVZK at the OracleReduct
- `theorem Reduction.isHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:583](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L583) — **Existential zero-error approximate honest-distribution transfer for exact HVZK.**

### `isHVZK_iff_isStatHVZK_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_iff_isStatHVZK_zero` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:174](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L174) — Perfect HVZK existence for oracle reductions is equivalent to zero-error statistical HVZK existence.
- `theorem Reduction.isHVZK_iff_isStatHVZK_zero` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:218](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L218) — **Perfect HVZK existence is equivalent to zero-error statistical HVZK existence.**

### `isHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:372](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L372) — **OracleReduction `isHVZK` from the symmetric-facing constant-simulator criterion.**
- `theorem Reduction.isHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:455](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L455) — **`isHVZK` from the symmetric-facing constant-simulator criterion.**

### `isHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:347](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L347) — **OracleReduction `isHVZK` from the constant-simulator criterion.**
- `theorem Reduction.isHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:432](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L432) — **`isHVZK` from the constant-simulator criterion.**

### `isPrimitiveRoot_zeta` (2 declarations, 2 files)

- `theorem R12J.General.isPrimitiveRoot_zeta` [ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean:171](../../../ArkLib/Data/CodingTheory/ProximityGap/JointT2Unconditional.lean#L171) — `zeta m` is a primitive `2^m`-th root of unity.
- `theorem Concrete.isPrimitiveRoot_zeta` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean:212](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungUnconditionalGeneral.lean#L212) — `zeta m` is a primitive `2^m`-th root of unity (`m ≥ 1`).

### `isStatHVZK` (2 declarations, 2 files)

- `def OracleReduction.isStatHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:71](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L71) — Existential statistical HVZK for an oracle reduction.
- `def Reduction.isStatHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:98](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L98) — A reduction is *statistically* honest-verifier zero-knowledge with error `ε` if some simulator achie

### `isStatHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:410](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L410) — **OracleReduction `isStatHVZK` transfers along an equal honest distribution.**
- `theorem Reduction.isStatHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:493](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L493) — **`isStatHVZK` transfers along an `evalDist`-equal honest distribution.**

### `isStatHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:436](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L436) — **OracleReduction `isStatHVZK` honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.isStatHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:518](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L518) — **`isStatHVZK` honest-distribution congruence with opposite-order equality.**

### `isStatHVZK.mono_error` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.mono_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:198](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L198) — `isStatHVZK` for oracle reductions is monotone in the error bound.
- `theorem Reduction.isStatHVZK.mono_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:240](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L240) — **`isStatHVZK` is monotone in the error.**

### `isStatHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:187](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L187) — `isStatHVZK` for oracle reductions is antitone in the relation.
- `theorem Reduction.isStatHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:230](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L230) — **`isStatHVZK` is antitone in the relation.**

### `isStatHVZK.mono_relation_error` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.mono_relation_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:261](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L261) — Existential statistical HVZK for oracle reductions transports across both relation restriction and e
- `theorem Reduction.isStatHVZK.mono_relation_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:295](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L295) — **Existential statistical HVZK transports across both relation restriction and error relaxation.** T

### `isStatHVZK.triangle_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:449](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L449) — **Existential approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.isStatHVZK.triangle_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:530](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L530) — **Existential approximate honest-distribution transfer for statistical HVZK.**

### `isStatHVZK.triangle_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:464](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L464) — **Existential symmetric-facing approximate honest-distribution transfer at the OracleReduction API b
- `theorem Reduction.isStatHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:543](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L543) — **Existential symmetric-facing approximate honest-distribution transfer.**

### `isStatHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:494](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L494) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for statistical H
- `theorem Reduction.isStatHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:570](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L570) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for statistical H

### `isStatHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:479](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L479) — **Existential zero-error approximate honest-distribution transfer for statistical HVZK at the Oracle
- `theorem Reduction.isStatHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:556](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L556) — **Existential zero-error approximate honest-distribution transfer for statistical HVZK.**

### `isStatHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:384](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L384) — **OracleReduction `isStatHVZK` from the symmetric-facing constant-simulator criterion.**
- `theorem Reduction.isStatHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:467](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L467) — **`isStatHVZK` from the symmetric-facing constant-simulator criterion.**

### `isStatHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:359](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L359) — **OracleReduction `isStatHVZK` from the constant-simulator criterion.**
- `theorem Reduction.isStatHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:443](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L443) — **`isStatHVZK` from the constant-simulator criterion.**

### `isStatHVZK_zero.isHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_zero.isHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:162](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L162) — Zero-error statistical HVZK existence for oracle reductions recovers perfect HVZK existence.
- `theorem Reduction.isStatHVZK_zero.isHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:208](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L208) — **Zero-error statistical HVZK existence is perfect HVZK existence.**

### `isStatHVZK_zero.isHVZK_mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_zero.isHVZK_mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:287](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L287) — Zero-error statistical HVZK existence for oracle reductions transports back to perfect HVZK existenc
- `theorem Reduction.isStatHVZK_zero.isHVZK_mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:315](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L315) — **Zero-error statistical HVZK existence transports back to perfect HVZK existence on a subrelation.*

### `iterated_fold_to_const_strict` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.iterated_fold_to_const_strict` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1303](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1303) — **Strict version**: When folding the last oracle to level `ℓ` (final sumcheck), the iterated fold of
- `lemma Binius.FRIBinius.CoreInteractionPhase.iterated_fold_to_const_strict` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:733](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L733) — Strict helper: folding the last oracle block in the final sumcheck step yields the constant function

### `johnson_radius_lt_capacity` (2 declarations, 2 files)

- `theorem ProximityGap.johnson_radius_lt_capacity` [ArkLib/Data/CodingTheory/ProximityGap/RSListDecodingFrontier.lean:62](../../../ArkLib/Data/CodingTheory/ProximityGap/RSListDecodingFrontier.lean#L62) — **The Johnson radius is strictly below the list-decoding capacity radius.** For a Reed–Solomon code
- `theorem ArkLib.ProximityGap.Issue232Bricks.johnson_radius_lt_capacity` [ArkLib/Data/CodingTheory/ProximityGap/VerifiedBricks.lean:156](../../../ArkLib/Data/CodingTheory/ProximityGap/VerifiedBricks.lean#L156) — **Strict Johnson–capacity separation.** For a rate `ρ ∈ (0,1)`, the RS Johnson radius `1 − √ρ` is *s

### `jointAgreeSet` (2 declarations, 2 files)

- `def ProximityPrizeCA.jointAgreeSet` [ArkLib/Data/CodingTheory/ProximityCA.lean:39](../../../ArkLib/Data/CodingTheory/ProximityCA.lean#L39) — The joint agreement set of two word pairs.
- `def Round17CAPair.jointAgreeSet` [ArkLib/Data/CodingTheory/ProximityGap/CAPairExtractionEngine.lean:56](../../../ArkLib/Data/CodingTheory/ProximityGap/CAPairExtractionEngine.lean#L56) — The joint agreement set of the pair `(f₁, f₂)` with the codeword pair `(g₁, g₂)`.

### `knowledgeSoundness.mono_error` (2 declarations, 2 files)

- `theorem Verifier.knowledgeSoundness.mono_error` [ArkLib/OracleReduction/Security/Basic.lean:381](../../../ArkLib/OracleReduction/Security/Basic.lean#L381) — Straightline knowledge soundness is monotone in the allowed knowledge error.
- `theorem Verifier.StateRestoration.knowledgeSoundness.mono_error` [ArkLib/OracleReduction/Security/StateRestoration.lean:218](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L218) — State-restoration knowledge soundness is monotone in the allowed knowledge-soundness error.

### `knowledgeSoundness.mono_relations` (2 declarations, 2 files)

- `theorem Verifier.knowledgeSoundness.mono_relations` [ArkLib/OracleReduction/Security/Basic.lean:397](../../../ArkLib/OracleReduction/Security/Basic.lean#L397) — Straightline knowledge soundness is monotone in the input and output relations. If knowledge soundne
- `theorem Verifier.StateRestoration.knowledgeSoundness.mono_relations` [ArkLib/OracleReduction/Security/StateRestoration.lean:232](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L232) — State-restoration knowledge soundness is monotone under enlarging the valid input relation and shrin

### `lagrangeCurve` (2 declarations, 2 files)

- `def CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.lagrangeCurve` [ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCaptureUD.lean:82](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCaptureUD.lean#L82) — The Lagrange curve tuple through the values `V` at the nodes `ν`: `a_j = ∑_t (ℓ_t).coeff j · V t`.
- `def ProximityGap.lagrangeCurve` [ArkLib/Data/CodingTheory/ProximityGap/Jo26CurveInterpolationRegime.lean:44](../../../ArkLib/Data/CodingTheory/ProximityGap/Jo26CurveInterpolationRegime.lean#L44) — The Lagrange coefficient stack through the values of `f` on `B`: the `j`-th curve coefficient is `∑_

### `lagrangeCurve_eval` (2 declarations, 2 files)

- `lemma CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.lagrangeCurve_eval` [ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCaptureUD.lean:97](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25CurveCaptureUD.lean#L97) — **The curve identity**: `∑_j C(γʲ)·a_j = ∑_t C(ℓ_t(γ))·V t`.
- `theorem ProximityGap.lagrangeCurve_eval` [ArkLib/Data/CodingTheory/ProximityGap/Jo26CurveInterpolationRegime.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/Jo26CurveInterpolationRegime.lean#L60) — **The interpolation identity.** For `β ∈ B` with `#B ≤ ℓ + 1`, the degree-`≤ ℓ` curve with the Lagra

### `lambda_le_ggr11_of_Lambda_top` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_Lambda_top` [ArkLib/ToMathlib/GGR11Interleaved.lean:404](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L404) — Generic end-to-end infinite-list regime: if the base list size is infinite and the Red budget is pos
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_Lambda_top` [ArkLib/ToMathlib/GGR11Reconnect.lean:134](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L134) — **Infinite-list regime, reconnected.** When the base list size is infinite and the GGR11 Red budget

### `lambda_le_ggr11_of_le_exp` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_le_exp` [ArkLib/ToMathlib/GGR11Interleaved.lean:394](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L394) — Generic end-to-end elementary regime: if the Red budget already dominates the interleaving factor, t
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_le_exp` [ArkLib/ToMathlib/GGR11Reconnect.lean:122](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L122) — **Elementary regime, reconnected.** When the GGR11 Red budget already dominates the interleaving fac

### `lambda_le_ggr11_of_perWordBound` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_perWordBound` [ArkLib/ToMathlib/GGR11Interleaved.lean:118](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L118) — **Reduction of the GGR11 interleaved list-size bound to its per-word form.** Given the per-received-
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_perWordBound` [ArkLib/ToMathlib/GGR11Reconnect.lean:110](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L110) — **Reconnect (per-word form).** The bare bound follows from the (coarser) per-received-word residual

### `lambda_le_ggr11_of_treeFrontier` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_treeFrontier` [ArkLib/ToMathlib/GGR11Interleaved.lean:291](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L291) — End-to-end GGR11 list-size bound from the granular named frontier.
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_treeFrontier` [ArkLib/ToMathlib/GGR11Reconnect.lean:100](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L100) — **Reconnect (named frontier form).** The bare bound follows from the granular per-received-word `GGR

### `lambda_le_ggr11_of_treeStructure` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_treeStructure` [ArkLib/ToMathlib/GGR11Interleaved.lean:283](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L283) — **End-to-end:** the GGR11 interleaved list-size bound from the refined tree-existence residual.
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_treeStructure` [ArkLib/ToMathlib/GGR11Reconnect.lean:90](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L90) — **Reconnect (tree-existence form).** The bare `InterleavedCode.lambda_le_ggr11` bound follows from t

### `leftpad` (2 declarations, 2 files)

- `def Fin.leftpad` [ArkLib/Data/Fin/Tuple/Defs.lean:96](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L96) — Pad a `Fin`-indexed vector on the left with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.leftpad` [ArkLib/Data/Matrix/Basic.lean:25](../../../ArkLib/Data/Matrix/Basic.lean#L25) — (no docstring)

### `lemma_5_10` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.BadEventDS.lemma_5_10` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:379](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L379) — CO25 Lemma 5.10, current trace-event form. If the combined bad event `E(tr)` does not occur, then th
- `theorem OracleSpec.QueryLog.BadEventDSPaper.lemma_5_10` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:355](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L355) — CO25 Lemma 5.10, current trace-event form. If the combined bad event `E(tr)` does not occur, then th

### `length_mainFoldedOracleMessageIdx` (2 declarations, 2 files)

- `lemma Whir302Checked.length_mainFoldedOracleMessageIdx` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:76](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L76) — Payload length of the folded-oracle message slot `i` is the cardinality of the next paper evaluation
- `lemma Whir302RBR.length_mainFoldedOracleMessageIdx` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:192](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L192) — Payload length of the folded-oracle message slot `i` is the cardinality of the next evaluation domai

### `liftContext_completeness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:242](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L242) — STATEMENT REPAIR (2026-06-04): completeness lifting now additionally takes the verifier's oracle-rou
- `theorem Reduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:777](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L777) — Lifting the reduction preserves completeness, assuming the lens satisfies its completeness condition

### `liftContext_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:291](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L291) — (no docstring)
- `theorem Verifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1058](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1058) — (no docstring)

### `liftContext_perfectCompleteness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:252](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L252) — (no docstring)
- `theorem Reduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:882](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L882) — (no docstring)

### `liftContext_rbr_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:337](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L337) — Lifting the oracle verifier preserves round-by-round knowledge soundness, assuming the lens satisfie
- `theorem Verifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1804](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1804) — (no docstring)

### `liftContext_rbr_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:311](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L311) — (no docstring)
- `theorem Verifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1555](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1555) — (no docstring)

### `liftContext_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:276](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L276) — Lifting the oracle verifier preserves soundness, assuming the lens satisfies its soundness condition
- `theorem Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:911](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L911) — Lifting a verifier context preserves soundness, assuming the lens satisfies its soundness conditions

### `liftM_optionT_run_eq_seam_right` (2 declarations, 2 files)

- `theorem Reduction.liftM_optionT_run_eq_seam_right` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean:75](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean#L75) — **`(liftM g).run = liftM g.run` across the `pSpec₂` challenge seam.** The `pSpec₂` analogue of `lift
- `theorem Verifier.liftM_optionT_run_eq_seam_right` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean:194](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean#L194) — (no docstring)

### `lift_oc_optionT_coh_right` (2 declarations, 2 files)

- `theorem Reduction.lift_oc_optionT_coh_right` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean:110](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean#L110) — **`OptionT`-lift coherence for a phase computation across the `pSpec₂` seam.** The `pSpec₂` analogue
- `theorem Verifier.lift_oc_optionT_coh_right` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean:177](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessMsgProof.lean#L177) — (no docstring)

### `lineAgreeSet` (2 declarations, 2 files)

- `def ProximityGap.lineAgreeSet` [ArkLib/Data/CodingTheory/Connections/GKL24FirstMoment.lean:106](../../../ArkLib/Data/CodingTheory/Connections/GKL24FirstMoment.lean#L106) — The agreement domain of the line `u₀ + γ • u₁` with a codeword `w`. GCXK/GKL maximal-domain argument
- `def ArkLib.ProximityGap.KKH26.lineAgreeSet` [ArkLib/Data/CodingTheory/ProximityGap/KKH26CensusLaw.lean:54](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26CensusLaw.lean#L54) — The agreement set of the line word `x ↦ x^r + λ·x^{r−1}` with the polynomial `q`, inside the evaluat

### `listAt` (2 declarations, 2 files)

- `def ArkLib.ProximityGap.RSPrizeDataPoint.listAt` [ArkLib/Data/CodingTheory/ProximityGap/RSListSizeDataPoint.lean:57](../../../ArkLib/Data/CodingTheory/ProximityGap/RSListSizeDataPoint.lean#L57) — The list-decoding list at agreement radius `a` for received word `w`, as a `Finset` of the coefficie
- `def RSAsymptKernel.listAt` [ArkLib/Data/CodingTheory/ProximityGap/RSMDSListBound.lean:202](../../../ArkLib/Data/CodingTheory/ProximityGap/RSMDSListBound.lean#L202) — The finite set ("list") of `RS[F,n,k]` codewords of weight at most `w`.

### `loc_eval_ne_zero` (2 declarations, 2 files)

- `lemma NormalRank.loc_eval_ne_zero` [ArkLib/Data/CodingTheory/ProximityGap/NormalRankSharpThreshold.lean:166](../../../ArkLib/Data/CodingTheory/ProximityGap/NormalRankSharpThreshold.lean#L166) — (no docstring)
- `lemma TopLine.loc_eval_ne_zero` [ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean:390](../../../ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean#L390) — (no docstring)

### `loc_eval_zero` (2 declarations, 2 files)

- `lemma NormalRank.loc_eval_zero` [ArkLib/Data/CodingTheory/ProximityGap/NormalRankSharpThreshold.lean:162](../../../ArkLib/Data/CodingTheory/ProximityGap/NormalRankSharpThreshold.lean#L162) — (no docstring)
- `lemma TopLine.loc_eval_zero` [ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean:386](../../../ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean#L386) — (no docstring)

### `loc_natDegree` (2 declarations, 2 files)

- `lemma NormalRank.loc_natDegree` [ArkLib/Data/CodingTheory/ProximityGap/NormalRankSharpThreshold.lean:57](../../../ArkLib/Data/CodingTheory/ProximityGap/NormalRankSharpThreshold.lean#L57) — (no docstring)
- `lemma TopLine.loc_natDegree` [ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean:73](../../../ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean#L73) — (no docstring)

### `localSeries_eq_aPDecoded` (2 declarations, 2 files)

- `theorem BCIKS20.Claim510Agreement.localSeries_eq_aPDecoded` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Agreement.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Agreement.lean#L63) — **Per-place Hensel uniqueness (App-A §5.2.6, `π_z(γ) = P_z`).**  The canonical local Hensel series e
- `theorem BCIKS20.Claim510AgreementSupply.localSeries_eq_aPDecoded` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AgreementSupply.lean:77](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AgreementSupply.lean#L77) — **Hensel uniqueness (BCIKS20 Step 6)**: the canonical local Hensel series equals the decoded surface

### `lookupEncodedMessageAlphaHat` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Hyb23Bricks.lookupEncodedMessageAlphaHat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean:96](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Hyb23Bricks.lean#L96) — **H23-1.** Looking up the encoded block for message index `j` in the flattened `EncodedMessagesBefor
- `def DuplexSpongeFS.TraceTransform.lookupEncodedMessageAlphaHat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean:123](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceTransform.lean#L123) — Looks up the encoded message block `α̂_j` from the flat list of extracted sponge queries.

### `map` (2 declarations, 2 files)

- `def AGM.GroupRepresentation.map` [ArkLib/AGM/Basic.lean:109](../../../ArkLib/AGM/Basic.lean#L109) — **Functoriality of representations under group homomorphisms.** A group hom `f : G →* H` transports
- `def Fin.map` [ArkLib/Data/Fin/Sigma.lean:499](../../../ArkLib/Data/Fin/Sigma.lean#L499) — (no docstring)

### `mapEquiv` (2 declarations, 2 files)

- `def Probability.SizeSubset.mapEquiv` [ArkLib/Data/Probability/Combinatorial.lean:92](../../../ArkLib/Data/Probability/Combinatorial.lean#L92) — Transport a size-`n` subset across an equivalence of ambient types.
- `def Probability.SizedSubset.mapEquiv` [ArkLib/Data/Probability/UniformSubset.lean:54](../../../ArkLib/Data/Probability/UniformSubset.lean#L54) — Map an `n`-element subset across an equivalence of ambient finite types.

### `markedCurveDecodable_of_curveDecodable` (2 declarations, 2 files)

- `theorem ProximityGap.CurveDec.markedCurveDecodable_of_curveDecodable` [ArkLib/Data/CodingTheory/ProximityGap/CurveDecodability.lean:423](../../../ArkLib/Data/CodingTheory/ProximityGap/CurveDecodability.lean#L423) — **Original ⟹ marked ([Jo26] Lemma 5.4 / Theorem 5.5, substantive half), conditional on `FarWordSuppl
- `theorem ProximityGap.markedCurveDecodable_of_curveDecodable` [ArkLib/Data/CodingTheory/ProximityGap/GG25MarkedEquivalence.lean:45](../../../ArkLib/Data/CodingTheory/ProximityGap/GG25MarkedEquivalence.lean#L45) — **[Jo26] Theorem 5.5, original → marked.** For an additive code with `b ≤ a ≤ q`, [GG25] curve decod

### `masterKStateCore` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.masterKStateCore` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1680](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1680) — Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event of the `i-th` oracle if
- `def RingSwitching.masterKStateCore` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:499](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L499) — (no docstring)

### `masterKStateProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.masterKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1694](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1694) — (no docstring)
- `def RingSwitching.masterKStateProp` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:507](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L507) — (no docstring)

### `mcaBad` (2 declarations, 2 files)

- `def ProximityGap.mcaBad` [ArkLib/Data/CodingTheory/Connections/EpsMCABadGlue.lean:72](../../../ArkLib/Data/CodingTheory/Connections/EpsMCABadGlue.lean#L72) — For a fixed stack `(u₀, u₁)` and radius `δ`, the finset of "bad" scalars `γ ∈ F` for which the `mcaE
- `def R15MCAGap.mcaBad` [ArkLib/Data/CodingTheory/ProximityGap/MCABadScalarSpreadBridge.lean:82](../../../ArkLib/Data/CodingTheory/ProximityGap/MCABadScalarSpreadBridge.lean#L82) — The MCA bad event at scalar `γ`: the pencil word `f1 + γ·f2` is close to the code, yet the pair `(f1

### `mcaBadCount` (2 declarations, 2 files)

- `def ProximityGap.mcaBadCount` [ArkLib/Data/CodingTheory/ProximityGap/MCABadCount.lean:45](../../../ArkLib/Data/CodingTheory/ProximityGap/MCABadCount.lean#L45) — The number of bad scalars `γ : F` realising the MCA event for the pair `(u₀, u₁)` at radius `δ`.
- `def R15MCAGap.mcaBadCount` [ArkLib/Data/CodingTheory/ProximityGap/MCABadScalarSpreadBridge.lean:96](../../../ArkLib/Data/CodingTheory/ProximityGap/MCABadScalarSpreadBridge.lean#L96) — The number of MCA-bad scalars on the pencil through `f1` in direction `f2`.

### `mcaEventGSrow_badStack` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.mcaEventGSrow_badStack` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean:36](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean#L36) — **Key lemma.** For any nonzero codeword `w₀ ∈ C` and any `δ ≤ 1`, the GS-row bad event fires at the
- `theorem mcaEventGSrow_badStack` [ArkLib/MCAGSRefutationCore.lean:35](../../../ArkLib/MCAGSRefutationCore.lean#L35) — **Key lemma.** For any nonzero codeword `w₀ ∈ C` and any `δ ≤ 1`, the GS-row bad event fires at the

### `mcaEvent_g0` (2 declarations, 2 files)

- `theorem ProximityGap.DeltaStarExactPin.mcaEvent_g0` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean:164](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean#L164) — `γ = 0` is bad: the line is `u₀` itself, which agrees with the zero codeword on `S = {0,1,2}`, while
- `theorem ProximityGap.MCADeltaStarExactPoint.mcaEvent_g0` [ArkLib/Data/CodingTheory/ProximityGap/MCADeltaStarExactPoint.lean:239](../../../ArkLib/Data/CodingTheory/ProximityGap/MCADeltaStarExactPoint.lean#L239) — `γ = 0`, witness `S = {0,1,2}`, on-line codeword `0`; no pair: `u₁` is not interpolable on `S` (`a+b

### `mcaEvent_g2` (2 declarations, 2 files)

- `theorem ProximityGap.DeltaStarExactPin.mcaEvent_g2` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean:170](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean#L170) — `γ = 2` is bad, witness set `{0,2,3}`, interpolating codeword `1 + 4X`.
- `theorem ProximityGap.MCADeltaStarExactPoint.mcaEvent_g2` [ArkLib/Data/CodingTheory/ProximityGap/MCADeltaStarExactPoint.lean:253](../../../ArkLib/Data/CodingTheory/ProximityGap/MCADeltaStarExactPoint.lean#L253) — `γ = 2`, witness `S = {0,2,3}`, on-line codeword `1 + 4·x`; no pair: `u₀` is not interpolable on `S`

### `mcaEvent_g3` (2 declarations, 2 files)

- `theorem ProximityGap.DeltaStarExactPin.mcaEvent_g3` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean:176](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean#L176) — `γ = 3` is bad, witness set `{1,2,3}`, interpolating codeword `2 + 4X`.
- `theorem ProximityGap.MCADeltaStarExactPoint.mcaEvent_g3` [ArkLib/Data/CodingTheory/ProximityGap/MCADeltaStarExactPoint.lean:268](../../../ArkLib/Data/CodingTheory/ProximityGap/MCADeltaStarExactPoint.lean#L268) — `γ = 3`, witness `S = {1,2,3}`, on-line codeword `2 + 4·x`; no pair: `u₀` is not interpolable on `S`

### `mcaEvent_g4` (2 declarations, 2 files)

- `theorem ProximityGap.DeltaStarExactPin.mcaEvent_g4` [ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean:182](../../../ArkLib/Data/CodingTheory/ProximityGap/DeltaStarExactPinF5.lean#L182) — `γ = 4` is bad, witness set `{0,1,3}`, interpolating codeword `0`.
- `theorem ProximityGap.MCADeltaStarExactPoint.mcaEvent_g4` [ArkLib/Data/CodingTheory/ProximityGap/MCADeltaStarExactPoint.lean:283](../../../ArkLib/Data/CodingTheory/ProximityGap/MCADeltaStarExactPoint.lean#L283) — `γ = 4`, witness `S = {0,1,3}`, on-line codeword `0`; no pair: `u₀` is not interpolable on `S`.

### `mem_C_iff` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.mem_C_iff` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:49](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L49) — Membership in `C` is membership in the explicit three-element set.
- `theorem JohnsonBound.JqlRefutation.mem_C_iff` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:89](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L89) — Membership in `C` is membership in the explicit three-element set.

### `mem_gsSupport` (2 declarations, 2 files)

- `lemma GSHasse.mem_gsSupport` [ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean:81](../../../ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean#L81) — (no docstring)
- `lemma GSInterp.mem_gsSupport` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:67](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L67) — (no docstring)

### `mem_iff_loc_eval_zero` (2 declarations, 2 files)

- `lemma NormalRank.mem_iff_loc_eval_zero` [ArkLib/Data/CodingTheory/ProximityGap/NormalRankSharpThreshold.lean:273](../../../ArkLib/Data/CodingTheory/ProximityGap/NormalRankSharpThreshold.lean#L273) — (no docstring)
- `lemma TopLine.mem_iff_loc_eval_zero` [ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean:396](../../../ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean#L396) — (no docstring)

### `mem_support_oracleVerifier_run_oStmt` (2 declarations, 2 files)

- `theorem Sumcheck.Spec.mem_support_oracleVerifier_run_oStmt` [ArkLib/ProofSystem/Spartan/SumcheckPhaseRbr.lean:231](../../../ArkLib/ProofSystem/Spartan/SumcheckPhaseRbr.lean#L231) — **Reachable outputs of the (plain-verifier view of the) sum-check oracle verifier carry the unchange
- `theorem Sumcheck.Spec.SingleRound.mem_support_oracleVerifier_run_oStmt` [ArkLib/ProofSystem/Sumcheck/Spec/PinnedCompleteness.lean:167](../../../ArkLib/ProofSystem/Sumcheck/Spec/PinnedCompleteness.lean#L167) — **Per-round oracle pass-through.** Any statement in the support of the (plain-verifier view of the)

### `mem_support_simulateQ_id'_liftM_query` (2 declarations, 2 files)

- `lemma OptionT.mem_support_simulateQ_id'_liftM_query` [ArkLib/ToVCVio/Lemmas.lean:430](../../../ArkLib/ToVCVio/Lemmas.lean#L430) — **Generic**: any element of the range of a query is in the support of `simulateQ (fun t => liftM (qu
- `lemma mem_support_simulateQ_id'_liftM_query` [ArkLib/ToVCVio/Simulation.lean:217](../../../ArkLib/ToVCVio/Simulation.lean#L217) — (no docstring)

### `minDist_C` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.minDist_C` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:54](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L54) — Every distinct pair of codewords has Hamming distance `≥ 1`, and the pair `(c0, c1)` attains `1`. He
- `theorem JohnsonBound.JqlRefutation.minDist_C` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:97](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L97) — **`Code.minDist C = 1`.**  The defining set of distinct-pair distances is `{1, 2}` (`d(c0,c1) = d(c0

### `minpoly_adjoin_coprime_eq_cyclotomic` (2 declarations, 2 files)

- `theorem CoprimePacketMinpoly.minpoly_adjoin_coprime_eq_cyclotomic` [ArkLib/Data/CodingTheory/ProximityGap/CoprimePacketMinpoly.lean:52](../../../ArkLib/Data/CodingTheory/ProximityGap/CoprimePacketMinpoly.lean#L52) — **The coprime packet minimal polynomial**: over `K = ℚ⟮ξ⟯` with `ξ` a primitive `m`-th root of unity
- `theorem DeBruijnIntRelations.minpoly_adjoin_coprime_eq_cyclotomic` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntRelations.lean:177](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntRelations.lean#L177) — **The coprime cyclotomic minpoly, general orders**: for coprime `M, N ≥ 1` and primitive roots `ξ` (

### `minpoly_adjoin_primitiveRoot_eq_packet` (2 declarations, 2 files)

- `theorem CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet` [ArkLib/Data/CodingTheory/ProximityGap/CRTPacketMinpoly.lean:65](../../../ArkLib/Data/CodingTheory/ProximityGap/CRTPacketMinpoly.lean#L65) — **The packet minimal polynomial over the coprime cyclotomic extension** — the de Bruijn capstone ste
- `theorem DeBruijnTwoPrime.minpoly_adjoin_primitiveRoot_eq_packet` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnTwoPrime.lean:373](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnTwoPrime.lean#L373) — **The packet minimal polynomial over the coprime cyclotomic extension**: for distinct primes `p ≠ q`

### `mk_eq_trunc_of_tail_zero` (2 declarations, 2 files)

- `theorem ArkLib.BetaToCurveCoeffPolys.mk_eq_trunc_of_tail_zero` [ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean:86](../../../ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean#L86) — A power series whose coefficients vanish from index `k` on **is** (the coercion of) its `k`-truncati
- `theorem PowerSeries.mk_eq_trunc_of_tail_zero` [ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean:77](../../../ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean#L77) — A power series whose coefficients vanish from index `k` on equals the coercion of its `k`-truncation

### `mono` (2 declarations, 2 files)

- `theorem CodingTheory.SlackThetaInvLog.mono` [ArkLib/ToMathlib/KK25NearCapacityProof.lean:71](../../../ArkLib/ToMathlib/KK25NearCapacityProof.lean#L71) — A `Θ(1/log n)` certificate widens to any larger constant bracket.
- `theorem ArkLib.SectionNewtonCleared.Cleared.mono` [ArkLib/ToMathlib/SectionNewtonCleared.lean:78](../../../ArkLib/ToMathlib/SectionNewtonCleared.lean#L78) — (no docstring)

### `msgAns` (2 declarations, 2 files)

- `def StirIOP.MultiRound.msgAns` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:184](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L184) — The honest answer of a message oracle (ascribed at `F`).
- `def Whir302Checked.msgAns` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:125](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L125) — The honest answer of a message oracle (ascribed at `F`).

### `multilinearWeight` (2 declarations, 2 files)

- `def multilinearWeight` [ArkLib/Data/CodingTheory/Prelims.lean:23](../../../ArkLib/Data/CodingTheory/Prelims.lean#L23) — The tensor product weight `⊗_{i=0}^{ϑ-1}(1 - rᵢ, rᵢ)` for a specific index `i` given randomness `r`.
- `def Issue33Binius.multilinearWeight` [ArkLib/ProofSystem/Binius/BinaryBasefold/MultilinearWeightRecursion.lean:24](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/MultilinearWeightRecursion.lean#L24) — Tensor product weight `⊗_{j<ϑ}(1 - r_j, r_j)` at index `i` given challenges `r`. This is a verbatim

### `myH` (2 declarations, 2 files)

- `abbrev BCIKS20.HenselNumerator.WeightWitness.myH` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:39](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L39) — Monic separable irreducible `H = Y² − 2` over `(ZMod 3)[X]`.
- `abbrev BCIKS20.HenselNumerator.Witness.myH` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:45](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L45) — Non-monic irreducible `H = 2·Y` over `ℚ[X]` (leading coeff `2`, a unit ⟹ associate of `Y`).

### `myH_irreducible` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myH_irreducible` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:72](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L72) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myH_irreducible` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:72](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L72) — (no docstring)

### `myH_leadingCoeff` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myH_leadingCoeff` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:59](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L59) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myH_leadingCoeff` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:64](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L64) — (no docstring)

### `myH_natDegree` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myH_natDegree` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:53](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L53) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myH_natDegree` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L60) — (no docstring)

### `myH_separable` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myH_separable` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:89](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L89) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myH_separable` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:96](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L96) — (no docstring)

### `myHyp` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myHyp` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:102](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L102) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myHyp` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:102](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L102) — (no docstring)

### `myR` (2 declarations, 2 files)

- `abbrev BCIKS20.HenselNumerator.WeightWitness.myR` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:43](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L43) — `R = Y² − 2 + u·s` (`u` = lift var, `s` = ground var): the high lift-direction degree breaks the wei
- `abbrev BCIKS20.HenselNumerator.Witness.myR` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:48](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L48) — Witness `R = X_mid²·Y² + 2·Y + X_mid` in `ℚ[X][X][Y]`.

### `myR_natDegree` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.WeightWitness.myR_natDegree` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean:79](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P1MonicWeightRefutation.lean#L79) — (no docstring)
- `lemma BCIKS20.HenselNumerator.Witness.myR_natDegree` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean:92](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2OrderZeroRefutationWitness.lean#L92) — (no docstring)

### `natDegree_lt_of_mem_degreeLT` (2 declarations, 2 files)

- `lemma ReedSolomon.natDegree_lt_of_mem_degreeLT` [ArkLib/Data/CodingTheory/ReedSolomon.lean:118](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L118) — (no docstring)
- `lemma Fri.Spec.Completeness.natDegree_lt_of_mem_degreeLT` [ArkLib/ToMathlib/FriCompleteFinalRound.lean:43](../../../ArkLib/ToMathlib/FriCompleteFinalRound.lean#L43) — A `CPolynomial` in `degreeLT D` (for positive `D`) has `natDegree < D`. Bridges the FRI final-round

### `natDegree_minpoly_adjoin_coprime` (2 declarations, 2 files)

- `theorem CoprimePacketMinpoly.natDegree_minpoly_adjoin_coprime` [ArkLib/Data/CodingTheory/ProximityGap/CoprimePacketMinpoly.lean:133](../../../ArkLib/Data/CodingTheory/ProximityGap/CoprimePacketMinpoly.lean#L133) — **The coprime tower degree**: adjoining a primitive `r`-th root to the coprime cyclotomic field gene
- `theorem DeBruijnIntRelations.natDegree_minpoly_adjoin_coprime` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntRelations.lean:184](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntRelations.lean#L184) — The degree extraction: `[ℚ(ζ_M)(ζ_N) : ℚ(ζ_M)] = φ(N)` for coprime orders.

### `natDegree_taylor_lt` (2 declarations, 2 files)

- `theorem ArkLib.BetaToCurveCoeffPolys.natDegree_taylor_lt` [ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean:141](../../../ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean#L141) — Taylor shift preserves the strict degree bound of a coefficient profile.
- `theorem Polynomial.natDegree_taylor_lt` [ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean:67](../../../ArkLib/ToMathlib/PolynomialCombinatorialAuxiliary.lean#L67) — A strict degree bound transports through a Taylor shift.

### `nearCertainBadLine_of_allButOne` (2 declarations, 2 files)

- `theorem CodingTheory.Bridge.AllButOne.nearCertainBadLine_of_allButOne` [ArkLib/ToMathlib/BGKS20AllButOne.lean:86](../../../ArkLib/ToMathlib/BGKS20AllButOne.lean#L86) — **"All but one scalar" producer (BGKS20 line-witness shape).** Given a stack `u` that is **not** joi
- `theorem CodingTheory.Bridge.nearCertainBadLine_of_allButOne` [ArkLib/ToMathlib/NearCertainBadLineProof.lean:84](../../../ArkLib/ToMathlib/NearCertainBadLineProof.lean#L84) — **All-but-one producer for `NearCertainBadLine`.** If a stack is not jointly close and every scalar

### `nodal_ne_zero` (2 declarations, 2 files)

- `theorem Round21Relations.nodal_ne_zero` [ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueRelationModule.lean:71](../../../ArkLib/Data/CodingTheory/ProximityGap/Conjecture41CliqueRelationModule.lean#L71) — The nodal polynomial is nonzero.
- `theorem Round27Core.nodal_ne_zero` [ArkLib/Data/CodingTheory/ProximityGap/RigiditySunflowerCore.lean:49](../../../ArkLib/Data/CodingTheory/ProximityGap/RigiditySunflowerCore.lean#L49) — (no docstring)

### `nonvacuity_zmod5` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.Round9SubgroupQuadraticHalving.nonvacuity_zmod5` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupQuadraticHalving.lean:212](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupQuadraticHalving.lean#L212) — **Non-vacuity witness.** Over `F = ZMod 5`, `2` is a primitive `4`-th root of unity (`2¹=2, 2²=4, 2³
- `theorem ArkLib.ProximityGap.Round8SeamARecursion.nonvacuity_zmod5` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupSquaresHalvingRecursion.lean:261](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupSquaresHalvingRecursion.lean#L261) — **Non-vacuity: a concrete order-`4` smooth subgroup whose squares are the order-`2` subgroup.** Over

### `nonvacuous_zmod13` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round8FullConcentration.nonvacuous_zmod13` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorQIndependentNegSymm.lean:375](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorQIndependentNegSymm.lean#L375) — **Non-vacuity (concrete `ZMod 13`, `D = id`, `H = {1,2,3}`, `t = 2`, `k = 3`).** With `ι = ZMod 13`,
- `theorem ArkLib.CodingTheory.Round7Concentration.nonvacuous_zmod13` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumNegSymmConcentration.lean:312](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumNegSymmConcentration.lean#L312) — **Non-vacuity (the bound is genuine, not `0 ≤ …`).** Over `F = ZMod 13` (`13` prime, `(2:ZMod 13) ≠

### `notFunction` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.BadEventDS.notFunction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:215](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L215) — (no docstring)
- `def OracleSpec.QueryLog.BadEventDSPaper.notFunction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:191](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L191) — (no docstring)

### `not_collisionPerm_of_not_combined` (2 declarations, 2 files)

- `lemma OracleSpec.QueryLog.BadEventDS.not_collisionPerm_of_not_combined` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean:295](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEvents.lean#L295) — (no docstring)
- `lemma OracleSpec.QueryLog.BadEventDSPaper.not_collisionPerm_of_not_combined` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:271](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L271) — (no docstring)

### `not_exists_lt_floor_eq_of_lattice` (2 declarations, 2 files)

- `theorem ArkLib.Issue64Boundary.not_exists_lt_floor_eq_of_lattice` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardLatticeSlice.lean:112](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardLatticeSlice.lean#L112) — **The strict-below same-floor witness set is empty at a lattice point.**  Direct corollary of `floor
- `theorem ArkLib.BoundaryCardResidual.not_exists_lt_floor_eq_of_lattice` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean:186](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean#L186) — **No strict sub-radius has the same floor at a lattice endpoint.**  This records the precise failure

### `not_johnson_at_quarter` (2 declarations, 2 files)

- `theorem ArkLib.RemainingCoreWitness.not_johnson_at_quarter` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/RemainingCore.lean:201](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/RemainingCore.lean#L201) — At the canonical floor-matched radius `δ' = 1/4` the Johnson-side hypothesis `(1 − ρ)/2 < δ'` fails
- `theorem ArkLib.ClosedBoundaryFaithfulFloorCellWitness.not_johnson_at_quarter` [ArkLib/ToMathlib/ClosedBoundaryFaithfulFloorCell.lean:363](../../../ArkLib/ToMathlib/ClosedBoundaryFaithfulFloorCell.lean#L363) — At the cell radius `δ'' = 1/4` the Johnson-side hypothesis fails *exactly*: `(1 − ρ)/2 = (1 − 1/2)/2

### `not_uniformEpsMCAgsPrizeBoundConjecture` (2 declarations, 2 files)

- `theorem ProximityGap.MCAGSPrizeRefutation.not_uniformEpsMCAgsPrizeBoundConjecture` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean:102](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSRefutation.lean#L102) — **MAIN THEOREM (#141): the formalized uniform prize conjecture is FALSE.** `uniformEpsMCAgsPrizeBoun
- `theorem not_uniformEpsMCAgsPrizeBoundConjecture` [ArkLib/MCAGSRefutationCore.lean:101](../../../ArkLib/MCAGSRefutationCore.lean#L101) — **MAIN THEOREM (#141): the formalized uniform prize conjecture is FALSE.** `uniformEpsMCAgsPrizeBoun

### `odd_psum_vanish` (2 declarations, 2 files)

- `theorem Round28FullWindow.odd_psum_vanish` [ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean:54](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean#L54) — **Odd power sums vanish identically on antipodally-closed sets** (the Round-8 engine at `ω = −1`): p
- `theorem Round26Recursion.odd_psum_vanish` [ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean:52](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean#L52) — **Odd power sums vanish identically on antipodally-closed sets** (the Round-8 engine at `ω = −1`): p

### `one_le_Lambda_of_nonempty` (2 declarations, 2 files)

- `theorem CodingTheory.one_le_Lambda_of_nonempty` [ArkLib/Data/CodingTheory/ListSizeVolumeBound.lean:184](../../../ArkLib/Data/CodingTheory/ListSizeVolumeBound.lean#L184) — **List-size lower bound `1 ≤ \|Λ(C,δ)\|` for a nonempty code and `δ ≥ 0`.** Any codeword is `0`-close
- `lemma InterleavedCode.GGR11.one_le_Lambda_of_nonempty` [ArkLib/ToMathlib/GGR11TreeConstruction.lean:1247](../../../ArkLib/ToMathlib/GGR11TreeConstruction.lean#L1247) — With a nonempty code, a nonnegative radius, and finite lists, the maximised list size is at least on

### `openingPSpec` (2 declarations, 2 files)

- `def SimpleRO.openingPSpec` [ArkLib/CommitmentScheme/SimpleRO.lean:56](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L56) — (no docstring)
- `abbrev Commitment.Transparent.openingPSpec` [ArkLib/CommitmentScheme/Transparent.lean:45](../../../ArkLib/CommitmentScheme/Transparent.lean#L45) — The one-message protocol specification of the transparent opening: the prover sends a single (conten

### `oracleProver_run` (2 declarations, 2 files)

- `theorem SendSingleWitness.oracleProver_run` [ArkLib/ProofSystem/Component/SendWitness.lean:396](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L396) — (no docstring)
- `lemma CheckClaim.oracleProver_run` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:61](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L61) — The oracle `CheckClaim` prover is a deterministic pass-through: empty transcript, unchanged statemen

### `oracleVerifier_rbrSoundness` (2 declarations, 2 files)

- `theorem Sumcheck.Spec.oracleVerifier_rbrSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/OracleRbrSoundness.lean:107](../../../ArkLib/ProofSystem/Sumcheck/Spec/OracleRbrSoundness.lean#L107) — **Oracle-level multi-round round-by-round (plain) soundness of the generic sum-check oracle verifier
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRoundFlipImpClose.lean:46](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRoundFlipImpClose.lean#L46) — **Per-round plain RBR soundness, discharged for the single-round sum-check oracle verifier.** This c

### `oracleVerifier_toVerifier_run` (2 declarations, 2 files)

- `theorem ReduceClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/ReduceClaim.lean:267](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L267) — Running the (oracle) verifier of the `ReduceClaim` oracle reduction deterministically returns the ma
- `theorem SendSingleWitness.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendWitness.lean:404](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L404) — (no docstring)

### `p6_deg` (2 declarations, 2 files)

- `lemma ArkLib.CodingTheory.TinyInteriorK3.p6_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:148](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L148) — (no docstring)
- `lemma ArkLib.CodingTheory.Round3SmoothF17.p6_deg` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:158](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L158) — (no docstring)

### `pSpecCoreInteraction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:248](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L248) — (no docstring)
- `def RingSwitching.pSpecCoreInteraction` [ArkLib/ProofSystem/RingSwitching/Spec.lean:50](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L50) — (no docstring)

### `pSpecFold` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecFold` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:201](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L201) — (no docstring)
- `def Fri.Spec.pSpecFold` [ArkLib/ProofSystem/Fri/Spec/General.lean:66](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L66) — (no docstring)

### `pSpecSumcheckRound` (2 declarations, 2 files)

- `abbrev RingSwitching.pSpecSumcheckRound` [ArkLib/ProofSystem/RingSwitching/Spec.lean:41](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L41) — (no docstring)
- `def Sumcheck.Structured.pSpecSumcheckRound` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:256](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L256) — Protocol spec for one round of the structured sumcheck: P sends a degree-≤`d` univariate `h_i(X) ∈ L

### `pSpec_dir_zero` (2 declarations, 2 files)

- `theorem StirIOP.Round.pSpec_dir_zero` [ArkLib/ProofSystem/Stir/RoundProtocol.lean:65](../../../ArkLib/ProofSystem/Stir/RoundProtocol.lean#L65) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.pSpec_dir_zero` [ArkLib/ProofSystem/Sumcheck/Spec/Completeness.lean:70](../../../ArkLib/ProofSystem/Sumcheck/Spec/Completeness.lean#L70) — The sum-check round protocol leads with the prover's univariate-polynomial message.

### `pad` (2 declarations, 2 files)

- `def R1CS.pad` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:73](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L73) — Pad an R1CS instance (on the right) from `sz₁` to `sz₂` with zeros. Note that this results in trunca
- `theorem ArkLib.SectionNewtonCleared.Cleared.pad` [ArkLib/ToMathlib/SectionNewtonCleared.lean:83](../../../ArkLib/ToMathlib/SectionNewtonCleared.lean#L83) — (no docstring)

### `pair_rigidity` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.Round8PrizeSurvives.pair_rigidity` [ArkLib/Data/CodingTheory/ProximityGap/CollisionRigidityThreeSwap.lean:112](../../../ArkLib/Data/CodingTheory/ProximityGap/CollisionRigidityThreeSwap.lean#L112) — **Pair rigidity (the field input).** If `(2 : F) ≠ 0` and two `2`-element sets `{x₁,x₂}`, `{y₁,y₂}`
- `theorem Round23Rigidity.pair_rigidity` [ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean:157](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityBaseCasePairs.lean#L157) — **THE BASE-CASE RIGIDITY THEOREM.** Over a `CharZero` field with the half basis independent: if `sva

### `paperTranscriptVectorIOP_pureTrue_perfectCompleteness` (2 declarations, 2 files)

- `theorem Whir302.paperTranscriptVectorIOP_pureTrue_perfectCompleteness` [ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean:72](../../../ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean#L72) — (no docstring)
- `theorem Whir302RBR.paperTranscriptVectorIOP_pureTrue_perfectCompleteness` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:419](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L419) — (no docstring)

### `perfectCorrectness` (2 declarations, 2 files)

- `def Commitment.perfectCorrectness` [ArkLib/CommitmentScheme/Basic.lean:109](../../../ArkLib/CommitmentScheme/Basic.lean#L109) — A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
- `def CommitmentScheme.perfectCorrectness` [ArkLib/CommitmentScheme/CommitmentScheme.lean:74](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L74) — A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.

### `perfectHVZK` (2 declarations, 2 files)

- `def OracleReduction.perfectHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:44](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L44) — Perfect HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`.
- `def Reduction.perfectHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:69](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L69) — A reduction satisfies perfect honest-verifier zero-knowledge with respect to a simulator and relatio

### `perfectHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:33](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L33) — **OracleReduction perfect HVZK transfers along an equal honest distribution.**
- `theorem Reduction.perfectHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:64](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L64) — **Perfect HVZK transfers along an `evalDist`-equal honest distribution.** If two reductions have the

### `perfectHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:59](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L59) — **OracleReduction perfect HVZK honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.perfectHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:96](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L96) — **Perfect HVZK honest-distribution congruence with opposite-order equality.**

### `perfectHVZK.isHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:130](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L130) — **A concrete OracleReduction perfect-HVZK simulator witnesses existential HVZK.**
- `theorem Reduction.perfectHVZK.isHVZK` [ArkLib/ToMathlib/ZKTransferBricks.lean:174](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L174) — **A concrete perfect-HVZK simulator witnesses existential HVZK.**

### `perfectHVZK.isHVZK_of_simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK_of_simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:152](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L152) — **Package an OracleReduction perfect-HVZK proof after normalizing the simulator distribution.**
- `theorem Reduction.perfectHVZK.isHVZK_of_simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:194](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L194) — **Package a perfect-HVZK proof after normalizing the simulator distribution.**

### `perfectHVZK.isHVZK_of_simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:176](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L176) — **Package an OracleReduction perfect-HVZK proof after simulator normalization in the opposite direct
- `theorem Reduction.perfectHVZK.isHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:216](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L216) — **Package a perfect-HVZK proof after simulator normalization in the opposite direction.**

### `perfectHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:107](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L107) — Perfect HVZK for oracle reductions is antitone in the relation.
- `theorem Reduction.perfectHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:156](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L156) — **Perfect HVZK is antitone in the relation.** A simulator that matches the honest transcript distrib

### `perfectHVZK.simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:86](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L86) — **OracleReduction perfect HVZK is preserved under an equal simulator distribution.**
- `theorem Reduction.perfectHVZK.simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:123](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L123) — **Perfect HVZK is preserved under an `evalDist`-equal simulator.** Swapping in a simulator that prod

### `perfectHVZK.simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:108](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L108) — **OracleReduction perfect HVZK simulator congruence with opposite-order equality.**
- `theorem Reduction.perfectHVZK.simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:152](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L152) — **Perfect HVZK simulator congruence with opposite-order equality.**

### `perfectHVZK.statisticalHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.statisticalHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:96](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L96) — Perfect HVZK for oracle reductions implies statistical HVZK with any error bound.
- `theorem Reduction.perfectHVZK.statisticalHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:137](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L137) — Perfect HVZK implies statistical HVZK with any error `ε`.

### `perfectHVZK.statisticalHVZK_mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.statisticalHVZK_mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:224](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L224) — Perfect HVZK for oracle reductions transports to statistical HVZK on a subrelation at any error. The
- `theorem Reduction.perfectHVZK.statisticalHVZK_mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:262](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L262) — **Perfect HVZK transports to statistical HVZK on a subrelation at any error.** The same simulator is

### `perfectHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:283](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L283) — Symmetric-facing zero-error approximate honest-distribution transfer for perfect HVZK at the OracleR
- `theorem Reduction.perfectHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:362](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L362) — Symmetric-facing zero-error approximate honest-distribution transfer for perfect HVZK.

### `perfectHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:269](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L269) — **Zero-error approximate honest-distribution transfer for perfect HVZK at the OracleReduction API bo
- `theorem Reduction.perfectHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:342](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L342) — **Zero-error approximate honest-distribution transfer for perfect HVZK.** If the honest-transcript b

### `perfectHVZK_iff_statisticalHVZK_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_iff_statisticalHVZK_zero` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:85](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L85) — Perfect HVZK for oracle reductions is exactly statistical HVZK with error `0`.
- `theorem Reduction.perfectHVZK_iff_statisticalHVZK_zero` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:109](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L109) — Perfect HVZK is exactly statistical HVZK with error `0`.

### `perfectHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:321](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L321) — **Symmetric-facing OracleReduction constant-simulator criterion for perfect HVZK.**
- `theorem Reduction.perfectHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:406](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L406) — **Symmetric-facing constant-simulator criterion for perfect HVZK.**

### `perfectHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:296](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L296) — **OracleReduction constant-simulator criterion for perfect HVZK.**
- `theorem Reduction.perfectHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:380](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L380) — **Constant-simulator criterion for perfect HVZK.** If the honest transcript distribution is `evalDis

### `perfectlyCorrect` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Ajtai.InnerOuter.perfectlyCorrect` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Correctness.lean:198](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Correctness.lean#L198) — **Unconditional perfect correctness with the concrete binary decomposition.** Both message and inner
- `theorem ArkLib.Lattices.Ajtai.Simple.perfectlyCorrect` [ArkLib/CommitmentScheme/Ajtai/Simple/Correctness.lean:33](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Correctness.lean#L33) — Simple Ajtai commitments are correct on short messages: an honest commitment to a message accepted b

### `pi_z_aPre_eq_taylor_coeff` (2 declarations, 2 files)

- `theorem BCIKS20.Claim510Agreement.pi_z_aPre_eq_taylor_coeff` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Agreement.lean:82](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Agreement.lean#L82) — **The coefficient reading**: `π_z (aPre t)` is the `t`-th Taylor coefficient of the decoded surface
- `theorem BCIKS20.Claim510AgreementSupply.pi_z_aPre_eq_taylor_coeff` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AgreementSupply.lean:98](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AgreementSupply.lean#L98) — The composed coefficient reading: `π_z(aPre t)` is the `t`-th Taylor coefficient of the decoded surf

### `pow_eq_card_eq_zero_or_gcd` (2 declarations, 2 files)

- `theorem ProximityGap.MultiplicativeRigidity.pow_eq_card_eq_zero_or_gcd` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean#L63) — **Lemma 1 (monomial agreement / coset rigidity).** In a finite cyclic commutative group `G` of order
- `theorem MultiplicativeRigidity.pow_eq_card_eq_zero_or_gcd` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean:99](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean#L99) — **Coset rigidity / monomial agreement (core).** In a finite cyclic group `G` of order `n = Fintype.c

### `pow_inj_below_order` (2 declarations, 2 files)

- `lemma ArkLib.ProximityGap.DeepQuotientTransfer.pow_inj_below_order` [ArkLib/Data/CodingTheory/ProximityGap/DeepQuotientTransfer.lean:87](../../../ArkLib/Data/CodingTheory/ProximityGap/DeepQuotientTransfer.lean#L87) — Injectivity of `i ↦ g^i` below the order of `g`, for nonzero `g` in a field. (Local copy of the priv
- `lemma ArkLib.ProximityGap.KKH26.pow_inj_below_order` [ArkLib/Data/CodingTheory/ProximityGap/KKH26WitnessSpread.lean:79](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26WitnessSpread.lean#L79) — Injectivity of `i ↦ g^i` below the order of `g`, for nonzero `g` in a field (elementary cancellation

### `probEvent_bind_eq_one` (2 declarations, 2 files)

- `lemma OracleComp.probEvent_bind_eq_one` [ArkLib/OracleReduction/ProbOneBindCompose.lean:40](../../../ArkLib/OracleReduction/ProbOneBindCompose.lean#L40) — **Probability-one bind composition.** If `mx` satisfies `p` with probability `1`, and `f a` satisfie
- `theorem probEvent_bind_eq_one` [ArkLib/ToMathlib/ProbEventBindOne.lean:29](../../../ArkLib/ToMathlib/ProbEventBindOne.lean#L29) — **Two-stage perfect composition.** If `mx` produces an output satisfying `P` with probability 1, and

### `probEvent_optionT_mk_eq_elim` (2 declarations, 2 files)

- `lemma probEvent_optionT_mk_eq_elim` [ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessProof.lean:71](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSoundnessProof.lean#L71) — **`OptionT.mk` event = `Option.elim`-bad event on the underlying computation.** Bridges the soundnes
- `theorem Verifier.StateFunction.probEvent_optionT_mk_eq_elim` [ArkLib/OracleReduction/Security/RoundByRound.lean:292](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L292) — **`OptionT` probEvent as a success-conjunction on the underlying computation.**  An `OptionT ProbCom

### `probEvent_uniformSample_eq_Pr_uniform` (2 declarations, 2 files)

- `theorem RingSwitching.BatchingPhase.probEvent_uniformSample_eq_Pr_uniform` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:57](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L57) — Bridge the framework's `SampleableType` uniform sampler to the PMF uniform notation used by Schwartz
- `theorem RingSwitching.SumcheckPhase.probEvent_uniformSample_eq_Pr_uniform` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:63](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L63) — Bridge the framework's `SampleableType` uniform sampler to the PMF uniform notation used by some sta

### `prod_X_sub_C_injOn_subsets` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round4InteriorList.prod_X_sub_C_injOn_subsets` [ArkLib/Data/CodingTheory/ProximityGap/InteriorListCountBridge.lean:128](../../../ArkLib/Data/CodingTheory/ProximityGap/InteriorListCountBridge.lean#L128) — The two root products are equal as polynomials iff the subsets are equal (`D` injective).
- `theorem ArkLib.CodingTheory.CapacityLowerSharpen.prod_X_sub_C_injOn_subsets` [ArkLib/Data/CodingTheory/ProximityGap/ListCapacityFieldIndependent.lean:128](../../../ArkLib/Data/CodingTheory/ProximityGap/ListCapacityFieldIndependent.lean#L128) — The two root products are equal as polynomials iff the subsets are equal (`D` injective).

### `prop_4_23_singleRepetition_proximityCheck_bound` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.QueryPhase.prop_4_23_singleRepetition_proximityCheck_bound` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:2691](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L2691) — **Single Repetition Proximity Check Bound (Proposition 4.24)** For a single repetition of the proxim
- `theorem Binius.BinaryBasefold.prop_4_23_singleRepetition_proximityCheck_bound` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhaseSoundness.lean:1272](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhaseSoundness.lean#L1272) — **Proposition 4.24** (Query-phase soundness, assuming no bad events). If any oracle is non-compliant

### `proximityCondition` (2 declarations, 2 files)

- `def MutualCorrAgreement.proximityCondition` [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:56](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean#L56) — For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽` and linea
- `def Generator.proximityCondition` [ArkLib/ProofSystem/Whir/ProximityGen.lean:38](../../../ArkLib/ProofSystem/Whir/ProximityGen.lean#L38) — For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽ˡ` and linear

### `queryCodeword` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryCodeword` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean:91](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean#L91) — Oracle query helper: query a committed codeword at a given domain point. Restricted to codeword indi
- `def Fri.Spec.QueryRound.queryCodeword` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:1040](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L1040) — (no docstring)

### `queryOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:174](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L174) — The oracle reduction for the final query phase.
- `def Fri.Spec.QueryRound.queryOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:1158](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L1158) — (no docstring)

### `rate_eq_half` (2 declarations, 2 files)

- `theorem ArkLib.RemainingCoreWitness.rate_eq_half` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/RemainingCore.lean:190](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/RemainingCore.lean#L190) — The witness Reed–Solomon code has rate exactly `1/2` (`dim 2`, length `4`).
- `theorem ArkLib.ClosedBoundaryFaithfulFloorCellWitness.rate_eq_half` [ArkLib/ToMathlib/ClosedBoundaryFaithfulFloorCell.lean:351](../../../ArkLib/ToMathlib/ClosedBoundaryFaithfulFloorCell.lean#L351) — The witness Reed–Solomon code has rate exactly `1/2` (`dim 2`, length `4`).

### `rbrBudgetSet` (2 declarations, 2 files)

- `def Core2Keystone.rbrBudgetSet` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:57](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L57) — The WHIR per-challenge RBR budget set (verbatim shape from `Whir/RbrBudgetAccounting.lean`). Reprodu
- `def Issue113WHIR.rbrBudgetSet` [ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean:55](../../../ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean#L55) — The WHIR RBR budget set: the union of the four per-round budget families, as a `Finset ℝ≥0`. This is

### `rbrBudgetSet_nonempty` (2 declarations, 2 files)

- `theorem Core2Keystone.rbrBudgetSet_nonempty` [ArkLib/ProofSystem/Whir/KeystoneReduction.lean:63](../../../ArkLib/ProofSystem/Whir/KeystoneReduction.lean#L63) — (no docstring)
- `theorem Issue113WHIR.rbrBudgetSet_nonempty` [ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean:62](../../../ArkLib/ProofSystem/Whir/RbrBudgetAccounting.lean#L62) — The budget set is nonempty (it contains `ε_fin`). This is the side condition the in-tree `max' (by s

### `rbrExtractionFailureEvent` (2 declarations, 2 files)

- `def RingSwitching.BatchingPhase.rbrExtractionFailureEvent` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:911](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L911) — Extraction-failure/doom-escape event for the batching phase RBR proof.
- `def RingSwitching.SumcheckPhase.rbrExtractionFailureEvent` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:894](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L894) — Extraction failure implies a witness-dependent bad sumcheck event. The extracted `witMid` also carri

### `reduction_verifier_eq_verifier` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:193](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L193) — (no docstring)
- `lemma Sumcheck.Spec.SingleRound.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1401](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1401) — (no docstring)

### `redundantEntryDSPaper` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.redundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:45](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L45) — **Paper-faithful redundant entry (CO25 Def. 5.5).** An entry is redundant if a prior entry answers i
- `def DuplexSpongeFS.Paper.redundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:50](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L50) — Paper-faithful CO25 Definition 5.5: an entry is redundant iff a prior entry answers the same query —

### `relIn` (2 declarations, 2 files)

- `def CheckClaim.relIn` [ArkLib/ProofSystem/Component/CheckClaim.lean:61](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L61) — (no docstring)
- `def RandomQuery.relIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:44](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L44) — The input relation is that the two oracles are equal.

### `removeRedundantEntryDSPaper` (2 declarations, 2 files)

- `def OracleSpec.QueryLog.removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:62](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L62) — Remove paper-redundant entries by repeated erasure (classical choice of a redundant index), mirrorin
- `def DuplexSpongeFS.Paper.removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:72](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L72) — Paper-faithful dedup procedure: repeatedly erase a paper-redundant entry until none remain (verbatim

### `removeRedundantEntryDSPaper_eq_self` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.removeRedundantEntryDSPaper_eq_self` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:94](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L94) — Subtype fixpoint form for the canonical output.
- `theorem DuplexSpongeFS.Paper.removeRedundantEntryDSPaper_eq_self` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:105](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L105) — Subtype fixpoint form for the canonical output of `removeRedundantEntryDSPaper`.

### `removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:80](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L80) — `removeRedundantEntryDSPaper` is a fixpoint on already-deduplicated traces.
- `theorem DuplexSpongeFS.Paper.removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:91](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L91) — `removeRedundantEntryDSPaper` is a fixpoint on traces already satisfying `NoRedundantEntryDSPaper`.

### `removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean:88](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/BadEventsPaper.lean#L88) — First-projection form of the fixpoint lemma.
- `theorem DuplexSpongeFS.Paper.removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean:99](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEvents.lean#L99) — First-projection form of the fixpoint lemma.

### `rewindingKnowledgeSoundness` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.rewindingKnowledgeSoundness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:159](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L159) — Paper-facing alias for CO25 Definition 3.8 rewinding knowledge soundness.
- `def Verifier.rewindingKnowledgeSoundness` [ArkLib/OracleReduction/Security/Rewinding.lean:211](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L211) — CO25 Definition 3.8, adapted to ArkLib's non-interactive argument interface. ArkLib's `Prover.NARG`

### `rewindingKnowledgeSoundnessFamily` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.rewindingKnowledgeSoundnessFamily` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:176](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L176) — Paper-facing alias for CO25 Definition 3.8 with explicit security parameter `λ`.
- `def Verifier.rewindingKnowledgeSoundnessFamily` [ArkLib/OracleReduction/Security/Rewinding.lean:264](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L264) — CO25 Definition 3.8 with the security parameter `λ` made explicit as an external index. This is a wr

### `rightpad` (2 declarations, 2 files)

- `def Fin.rightpad` [ArkLib/Data/Fin/Tuple/Defs.lean:90](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L90) — Pad a `Fin`-indexed vector on the right with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.rightpad` [ArkLib/Data/Matrix/Basic.lean:21](../../../ArkLib/Data/Matrix/Basic.lean#L21) — (no docstring)

### `roundKnowledgeError` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckPhase.roundKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:252](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L252) — Repaired local bound for the current round-by-round proof. The degree-two bad-event lemma below is t
- `def Sumcheck.Structured.roundKnowledgeError` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:473](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L473) — Round-by-round knowledge error for a single round of the structured sumcheck: the Schwartz–Zippel bo

### `rsPoint_injective` (2 declarations, 2 files)

- `theorem ArkLib.KoalaBearAttack.rsPoint_injective` [ArkLib/ToMathlib/KoalaBearAttackInstance.lean:77](../../../ArkLib/ToMathlib/KoalaBearAttackInstance.lean#L77) — Distinct `Fin 4` points give distinct field points (characteristic `p > 4`).
- `theorem KoalaBear.rsPoint_injective` [ArkLib/ToMathlib/KoalaIRSAccounting.lean:66](../../../ArkLib/ToMathlib/KoalaIRSAccounting.lean#L66) — The four evaluation points `rsPoint j = (j.val : Sextic)` are pairwise distinct: each `j.val` is `<

### `rs_lambda_high_rate_jh01` (2 declarations, 2 files)

- `theorem CodingTheory.rs_lambda_high_rate_jh01` [ArkLib/Data/CodingTheory/ListDecoding/Bounds/RandomAndReedSolomon.lean:861](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds/RandomAndReedSolomon.lean#L861) — **ABF26 Theorem 3.14 [JH01 Thm 2], repaired list-size form.** Large-rate Reed-Solomon lower bound. F
- `theorem CodingTheory.ReedSolomon.rs_lambda_high_rate_jh01` [ArkLib/Data/CodingTheory/ListDecoding/JH01.lean:214](../../../ArkLib/Data/CodingTheory/ListDecoding/JH01.lean#L214) — ABF26 Theorem 3.14 / JH01 Theorem 2, in a repaired list-size form.  For every `j ≥ 2`, infinitely ma

### `run` (2 declarations, 2 files)

- `def AGM.Adversary.run` [ArkLib/AGM/Basic.lean:484](../../../ArkLib/AGM/Basic.lean#L484) — Running the adversary on a given table, returning the list of group elements it is supposed to outpu
- `def Prover.run` [ArkLib/OracleReduction/Execution.lean:97](../../../ArkLib/OracleReduction/Execution.lean#L97) — Run the prover in an interactive reduction. Returns the output statement and witness, and the transc

### `secondSCVP_mem_restrictDegree` (2 declarations, 2 files)

- `theorem Spartan.Spec.secondSCVP_mem_restrictDegree` [ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean:76](../../../ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean#L76) — The second sum-check virtual polynomial has degree `<= 2` per variable.
- `theorem Spartan.secondSCVP_mem_restrictDegree` [ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean:74](../../../ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean#L74) — **Degree bound of the second sum-check virtual polynomial** (`≤ 2` per variable): packages `ℳ(Y)` fo

### `seqCompose_perfectCompleteness_threaded` (2 declarations, 2 files)

- `theorem OracleReduction.seqCompose_perfectCompleteness_threaded` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeOracleCompleteness.lean:107](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeOracleCompleteness.lean#L107) — **n-ary message-seam `seqCompose` perfect completeness for oracle reductions (issue #29).** Every co
- `theorem Reduction.seqCompose_perfectCompleteness_threaded` [ArkLib/OracleReduction/Composition/Sequential/SeqComposePerfectCompletenessThreaded.lean:59](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposePerfectCompletenessThreaded.lean#L59) — **n-ary message-seam `seqCompose` perfect completeness, keystones inlined.** Every component is none

### `shiftSeries` (2 declarations, 2 files)

- `def ArkLib.Claim59Conditional.shiftSeries` [ArkLib/ToMathlib/BCIKS20PointwiseConditional.lean:53](../../../ArkLib/ToMathlib/BCIKS20PointwiseConditional.lean#L53) — The BCIKS shift series corresponding to the substitution $X \mapsto X - x_0$.
- `def ArkLib.SubstFieldCaveat.shiftSeries` [ArkLib/ToMathlib/SubstFieldCaveat.lean:75](../../../ArkLib/ToMathlib/SubstFieldCaveat.lean#L75) — The shift series corresponding to the substitution $X \mapsto X - x_0$.

### `simulateQ_askInput` (2 declarations, 2 files)

- `theorem StirIOP.MultiRound.simulateQ_askInput` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:248](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L248) — `simulateQ` collapse for the input-oracle query.
- `theorem Whir302Checked.simulateQ_askInput` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:447](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L447) — `simulateQ` collapse for an input-oracle query.

### `simulateQ_askList` (2 declarations, 2 files)

- `theorem StirIOP.MultiRound.simulateQ_askList` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:168](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L168) — If every step of an `askList` simulates to a pure value, the whole `askList` collapses to the corres
- `theorem Whir302Checked.simulateQ_askList` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:113](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L113) — If every step of an `askList` simulates to a pure value, the whole `askList` collapses to the corres

### `simulateQ_askMsg` (2 declarations, 2 files)

- `theorem StirIOP.MultiRound.simulateQ_askMsg` [ArkLib/ProofSystem/Stir/CheckingVerifier.lean:254](../../../ArkLib/ProofSystem/Stir/CheckingVerifier.lean#L254) — `simulateQ` collapse for a message-oracle query.
- `theorem Whir302Checked.simulateQ_askMsg` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:438](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L438) — `simulateQ` collapse for a message-oracle query.

### `simulateQ_optionT_failure'` (2 declarations, 2 files)

- `theorem Logup.simulateQ_optionT_failure'` [ArkLib/ProofSystem/Logup/Security/OuterRun.lean:52](../../../ArkLib/ProofSystem/Logup/Security/OuterRun.lean#L52) — `simulateQ` commutes with `OptionT` `failure`.
- `theorem RingSwitching.SumcheckPhase.simulateQ_optionT_failure'` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:102](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L102) — `simulateQ` commutes with `OptionT` `failure`, for an arbitrary lawful target monad `m` (so it appli

### `simulateQ_optionT_pure'` (2 declarations, 2 files)

- `theorem Logup.simulateQ_optionT_pure'` [ArkLib/ProofSystem/Logup/Security/OuterRun.lean:44](../../../ArkLib/ProofSystem/Logup/Security/OuterRun.lean#L44) — `simulateQ` commutes with `OptionT.pure`.
- `theorem RingSwitching.SumcheckPhase.simulateQ_optionT_pure'` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:91](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L91) — `simulateQ` commutes with `OptionT.pure` (no explicit empty-spec universes).

### `simulateQ_oracleVerify_eq` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.SingleRound.Simple.simulateQ_oracleVerify_eq` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:965](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L965) — Closed form of the simulated oracle-verifier `verify`: the inner `simOracle2` simulation collapses t
- `theorem ToyProblem.Spec.simulateQ_oracleVerify_eq` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:788](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L788) — **Closed form of the compiled toy-problem oracle verifier.** Simulating `oracleVerifier.verify` agai

### `simulateQ_simOracle2_query` (2 declarations, 2 files)

- `lemma RingSwitching.BatchingPhase.simulateQ_simOracle2_query` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:84](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L84) — OptionT/query form of `simulateQ_simOracle2_messageQuery`.
- `lemma RingSwitching.simulateQ_simOracle2_query` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1543](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1543) — **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as `simulateQ_s

### `simulateQ_simOracle_foldlM` (2 declarations, 2 files)

- `theorem simulateQ_simOracle_foldlM` [ArkLib/OracleReduction/SimOracleFoldlM.lean:27](../../../ArkLib/OracleReduction/SimOracleFoldlM.lean#L27) — If every step of a `foldlM` simulates (under the honest single-family oracle) to a pure value, the w
- `lemma Spartan.Spec.simulateQ_simOracle_foldlM` [ArkLib/ProofSystem/Spartan/SecondSumcheckFaithful.lean:75](../../../ArkLib/ProofSystem/Spartan/SecondSumcheckFaithful.lean#L75) — Simulating a `foldlM` whose every step simulates to a pure value collapses to the `foldl` of the pur

### `singleton_bound` (2 declarations, 2 files)

- `theorem singleton_bound` [ArkLib/Data/CodingTheory/Basic/LinearCode.lean:121](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean#L121) — **Singleton bound** for arbitrary codes
- `theorem ArkLib.CS25.singleton_bound` [ArkLib/Data/CodingTheory/SingletonBound.lean:30](../../../ArkLib/Data/CodingTheory/SingletonBound.lean#L30) — **Singleton bound.**  A code with minimum distance `≥ d` (`d ≥ 1`) has at most `q^(n−(d−1))` codewor

### `soundness.mono_error` (2 declarations, 2 files)

- `theorem Verifier.soundness.mono_error` [ArkLib/OracleReduction/Security/Basic.lean:315](../../../ArkLib/OracleReduction/Security/Basic.lean#L315) — Verifier soundness is monotone in the allowed soundness error.
- `theorem Verifier.StateRestoration.soundness.mono_error` [ArkLib/OracleReduction/Security/StateRestoration.lean:143](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L143) — State-restoration soundness is monotone in the allowed soundness error.

### `soundness.mono_languages` (2 declarations, 2 files)

- `theorem Verifier.soundness.mono_languages` [ArkLib/OracleReduction/Security/Basic.lean:331](../../../ArkLib/OracleReduction/Security/Basic.lean#L331) — Verifier soundness is monotone in the input and output languages. If soundness holds for a smaller h
- `theorem Verifier.StateRestoration.soundness.mono_languages` [ArkLib/OracleReduction/Security/StateRestoration.lean:157](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L157) — State-restoration soundness is monotone under enlarging the honest input language and shrinking the

### `sq_mem_half` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.Round9SubgroupQuadraticHalving.sq_mem_half` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupQuadraticHalving.lean:72](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupQuadraticHalving.lean#L72) — **Squaring lands in the half-order subgroup.** If `x ∈ μ_{2m}` (so `x^{2m}=1`) then `x² ∈ μ_m`, beca
- `theorem ArkLib.ProximityGap.Round8SeamARecursion.sq_mem_half` [ArkLib/Data/CodingTheory/ProximityGap/SubgroupSquaresHalvingRecursion.lean:98](../../../ArkLib/Data/CodingTheory/ProximityGap/SubgroupSquaresHalvingRecursion.lean#L98) — **Squaring lands in the half-order subgroup.** If `x ∈ G = nthRootsFinset (2m) 1` (so `x^{2m}=1`), t

### `sq_sum_le_card_support_mul_sum_sq` (2 declarations, 2 files)

- `theorem Finset.sq_sum_le_card_support_mul_sum_sq` [ArkLib/ToMathlib/SqSumCardSupport.lean:20](../../../ArkLib/ToMathlib/SqSumCardSupport.lean#L20) — (no docstring)
- `theorem ArkLib.sq_sum_le_card_support_mul_sum_sq` [ArkLib/ToMathlib/SupportSqBound.lean:25](../../../ArkLib/ToMathlib/SupportSqBound.lean#L25) — **Cauchy-Schwarz support bound.** Over a finite type, `(∑ f)² ≤ \|support f\| · (∑ f²)`.

### `sqrtRate_le_one` (2 declarations, 2 files)

- `theorem ArkLib.BoundaryCardResidualRefutation.sqrtRate_le_one` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualRefutation.lean:68](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidualRefutation.lean#L68) — (no docstring)
- `theorem ArkLib.BoundaryCardStrictInteriorRefutation.sqrtRate_le_one` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardStrictInteriorRefutation.lean:131](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardStrictInteriorRefutation.lean#L131) — (no docstring)

### `squares` (2 declarations, 2 files)

- `def Round28FullWindow.squares` [ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean:74](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean#L74) — The square set `A² = {x² : x ∈ A}`.
- `def Round26Recursion.squares` [ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean:72](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean#L72) — The square set `A² = {x² : x ∈ A}`.

### `squares_disjoint` (2 declarations, 2 files)

- `theorem Round28FullWindow.squares_disjoint` [ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean:133](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean#L133) — **Disjointness descends to the squares:** if `A, B` are antipodally closed and disjoint, then `A²` a
- `theorem Round26Recursion.squares_disjoint` [ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean:131](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean#L131) — **Disjointness descends to the squares:** if `A, B` are antipodally closed and disjoint, then `A²` a

### `squares_fiber` (2 declarations, 2 files)

- `theorem Round28FullWindow.squares_fiber` [ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean:78](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean#L78) — On an antipodally-closed set, the squaring map is exactly two-to-one: each fiber is the antipodal pa
- `theorem Round26Recursion.squares_fiber` [ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean:76](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean#L76) — On an antipodally-closed set, the squaring map is exactly two-to-one: each fiber is the antipodal pa

### `statisticalHVZK` (2 declarations, 2 files)

- `def OracleReduction.statisticalHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:53](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L53) — Statistical HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`.
- `def Reduction.statisticalHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:80](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L80) — A reduction satisfies statistical honest-verifier zero-knowledge with error `ε` if the simulator's t

### `statisticalHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:46](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L46) — **OracleReduction statistical HVZK transfers along an equal honest distribution.**
- `theorem Reduction.statisticalHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:80](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L80) — **Statistical HVZK transfers along an `evalDist`-equal honest distribution.** The same simulator and

### `statisticalHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:73](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L73) — **OracleReduction statistical HVZK honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.statisticalHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:109](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L109) — **Statistical HVZK honest-distribution congruence with opposite-order equality.**

### `statisticalHVZK.isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:141](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L141) — **A concrete OracleReduction statistical-HVZK simulator witnesses existential statistical HVZK.**
- `theorem Reduction.statisticalHVZK.isStatHVZK` [ArkLib/ToMathlib/ZKTransferBricks.lean:184](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L184) — **A concrete statistical-HVZK simulator witnesses existential statistical HVZK.**

### `statisticalHVZK.isStatHVZK_of_simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK_of_simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:164](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L164) — **Package an OracleReduction statistical-HVZK proof after normalizing the simulator distribution.**
- `theorem Reduction.statisticalHVZK.isStatHVZK_of_simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:205](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L205) — **Package a statistical-HVZK proof after normalizing the simulator distribution.**

### `statisticalHVZK.isStatHVZK_of_simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:188](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L188) — **Package an OracleReduction statistical-HVZK proof after simulator normalization in the opposite di
- `theorem Reduction.statisticalHVZK.isStatHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:227](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L227) — **Package a statistical-HVZK proof after simulator normalization in the opposite direction.**

### `statisticalHVZK.mono_error` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.mono_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:140](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L140) — Statistical HVZK for oracle reductions is monotone in the error bound.
- `theorem Reduction.statisticalHVZK.mono_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:188](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L188) — **Statistical HVZK is monotone in the error.** A simulator within total-variation distance `ε₁` is a

### `statisticalHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:129](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L129) — Statistical HVZK for oracle reductions is antitone in the relation.
- `theorem Reduction.statisticalHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:177](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L177) — **Statistical HVZK is antitone in the relation.**

### `statisticalHVZK.mono_relation_error` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.mono_relation_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:211](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L211) — Statistical HVZK for oracle reductions transports across both relation restriction and error relaxat
- `theorem Reduction.statisticalHVZK.mono_relation_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:250](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L250) — **Statistical HVZK transports across both relation restriction and error relaxation.**

### `statisticalHVZK.simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:97](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L97) — **OracleReduction statistical HVZK is preserved under an equal simulator distribution.**
- `theorem Reduction.statisticalHVZK.simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:138](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L138) — **Statistical HVZK is preserved under an `evalDist`-equal simulator.** Swapping in a simulator that

### `statisticalHVZK.simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:119](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L119) — **OracleReduction statistical HVZK simulator congruence with opposite-order equality.**
- `theorem Reduction.statisticalHVZK.simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:163](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L163) — **Statistical HVZK simulator congruence with opposite-order equality.**

### `statisticalHVZK.simulator_triangle` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_triangle` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:199](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L199) — **Triangle composition of statistical HVZK at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.simulator_triangle` [ArkLib/ToMathlib/ZKTransferBricks.lean:240](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L240) — **Triangle composition of statistical HVZK.** If `sim₁` is within `ε₁` of the honest distribution an

### `statisticalHVZK.triangle_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:213](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L213) — **Approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.triangle_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:265](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L265) — **Approximate honest-distribution transfer for statistical HVZK.** If a simulator is statistical-HVZ

### `statisticalHVZK.triangle_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:227](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L227) — **Symmetric-facing approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:291](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L291) — **Symmetric-facing approximate honest-distribution transfer.** This is the same result as `statistic

### `statisticalHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:255](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L255) — Symmetric-facing zero-error approximate honest-distribution transfer for statistical HVZK at the Ora
- `theorem Reduction.statisticalHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:324](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L324) — Symmetric-facing zero-error approximate honest-distribution transfer for statistical HVZK.

### `statisticalHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:241](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L241) — **Zero-error approximate honest-distribution transfer for statistical HVZK at the OracleReduction AP
- `theorem Reduction.statisticalHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:308](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L308) — **Zero-error approximate honest-distribution transfer for statistical HVZK.** If the honest transcri

### `statisticalHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:334](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L334) — **Symmetric-facing OracleReduction constant-simulator criterion for statistical HVZK.**
- `theorem Reduction.statisticalHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:419](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L419) — **Symmetric-facing constant-simulator criterion for statistical HVZK.**

### `statisticalHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:308](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L308) — **OracleReduction constant-simulator criterion for statistical HVZK.**
- `theorem Reduction.statisticalHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:394](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L394) — **Statistical constant-simulator criterion.** If the honest transcript distribution is `evalDist`-eq

### `statisticalHVZK_zero.perfectHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_zero.perfectHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:236](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L236) — Zero-error statistical HVZK for oracle reductions converts back to perfect HVZK for the same simulat
- `theorem Reduction.statisticalHVZK_zero.perfectHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:272](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L272) — **Zero-error statistical HVZK converts back to perfect HVZK for the same simulator.**

### `statisticalHVZK_zero.perfectHVZK_mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_zero.perfectHVZK_mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:248](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L248) — Zero-error statistical HVZK for oracle reductions transports back to perfect HVZK on a subrelation.
- `theorem Reduction.statisticalHVZK_zero.perfectHVZK_mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:283](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L283) — **Zero-error statistical HVZK transports back to perfect HVZK on a subrelation.** The same simulator

### `subdomainZeroEquiv` (2 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomainZeroEquiv` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:133](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L133) — The zeroth subdomain has the same finite set of field points as the ambient domain.
- `def Fri.subdomainZeroEquiv` [ArkLib/ProofSystem/BatchedFri/Security.lean:1626](../../../ArkLib/ProofSystem/BatchedFri/Security.lean#L1626) — The round-zero Batched FRI subdomain is equivalent to the original evaluation domain.

### `subgroup_mixed_sum_is_partial` (2 declarations, 2 files)

- `theorem ArkLib.ProximityGap.Round8CompleteSquare.subgroup_mixed_sum_is_partial` [ArkLib/Data/CodingTheory/ProximityGap/MixedGaussSumCompleteSquare.lean:192](../../../ArkLib/Data/CodingTheory/ProximityGap/MixedGaussSumCompleteSquare.lean#L192) — **The subgroup mixed sum is a PARTIAL sum — the open delimiter.** The complete-the-square reduction
- `theorem ArkLib.ProximityGap.Round8MixedGauss.subgroup_mixed_sum_is_partial` [ArkLib/Data/CodingTheory/ProximityGap/MixedGaussSumDiagonal.lean:206](../../../ArkLib/Data/CodingTheory/ProximityGap/MixedGaussSumDiagonal.lean#L206) — **The subgroup mixed sum is a PARTIAL Gauss sum — the open delimiter.** The collision count `M2` ove

### `sum_div_mul_prod_eq_sum_mul_prod_erase` (2 declarations, 2 files)

- `theorem Logup.sum_div_mul_prod_eq_sum_mul_prod_erase` [ArkLib/ProofSystem/Logup/Common.lean:755](../../../ArkLib/ProofSystem/Logup/Common.lean#L755) — (no docstring)
- `theorem Finset.sum_div_mul_prod_eq_sum_mul_prod_erase` [ArkLib/ToMathlib/ProtocolCountingBricks.lean:30](../../../ArkLib/ToMathlib/ProtocolCountingBricks.lean#L30) — **LogUp clear-denominators core.** `(∑ num/den)·(∏ den) = ∑ num·∏_{erase} den`.

### `sumcheckConsistencyProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.sumcheckConsistencyProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1449](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1449) — Sumcheck consistency: the claimed sumcheck target equals the sum of `H` over the boolean hypercube o
- `def Sumcheck.Structured.sumcheckConsistencyProp` [ArkLib/ProofSystem/Sumcheck/Structured.lean:212](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L212) — Sumcheck consistency: the claimed sum equals the actual polynomial evaluation sum over the evaluatio

### `sumcheckConsistency_at_last_simplifies` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.sumcheckConsistency_at_last_simplifies` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1163](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1163) — At `Fin.last ℓ`, sumcheck consistency is the single empty-variable evaluation.
- `lemma Binius.FRIBinius.CoreInteractionPhase.sumcheckConsistency_at_last_simplifies` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:685](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L685) — At `Fin.last ℓ'`, sumcheck consistency simplifies to a single evaluation.

### `sumcheckFoldOracleReduction` (2 declarations, 2 files)

- `def sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:805](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L805) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:155](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L155) — (no docstring)

### `sumcheckFoldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:910](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L910) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:253](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L253) — (no docstring)

### `sumcheckFoldOracleVerifier` (2 declarations, 2 files)

- `def sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:521](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L521) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:148](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L148) — (no docstring)

### `sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1064](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1064) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:443](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L443) — (no docstring)

### `support_mk` (2 declarations, 2 files)

- `lemma ReduceClaim.support_mk` [ArkLib/ProofSystem/Component/ReduceClaim.lean:181](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L181) — (no docstring)
- `lemma OptionT.support_mk` [ArkLib/ToVCVio/Lemmas.lean:106](../../../ArkLib/ToVCVio/Lemmas.lean#L106) — (no docstring)

### `synd` (2 declarations, 2 files)

- `def C2CoreBound.synd` [ArkLib/Data/CodingTheory/ProximityGap/C2CoreEliminationBound.lean:59](../../../ArkLib/Data/CodingTheory/ProximityGap/C2CoreEliminationBound.lean#L59) — The coefficient-window syndrome pairing: `⟨P, s⟩ = ∑_{j < N} P_j · s_j`.
- `def TopLine.synd` [ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean:52](../../../ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean#L52) — The coefficient-window syndrome pairing `⟨P, s⟩ = ∑_{j<N} P_j s_j`.

### `syndr` (2 declarations, 2 files)

- `def C2CoreBound.syndr` [ArkLib/Data/CodingTheory/ProximityGap/C2CoreEliminationBound.lean:65](../../../ArkLib/Data/CodingTheory/ProximityGap/C2CoreEliminationBound.lean#L65) — The `r`-shifted syndrome functional of a support.
- `def TopLine.syndr` [ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean:58](../../../ArkLib/Data/CodingTheory/ProximityGap/TopDirectionLineCount.lean#L58) — The `r`-shifted syndrome functional.

### `toMLE_evalC_eq_sum` (2 declarations, 2 files)

- `theorem Spartan.Spec.toMLE_evalC_eq_sum` [ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean:50](../../../ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean#L50) — (no docstring)
- `theorem Spartan.toMLE_evalC_eq_sum` [ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean:41](../../../ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean#L41) — **Polynomial-level partial evaluation of `Matrix.toMLE`.** Fixing the row variables at `r_x` yields

### `toMLE_evalC_mem_restrictDegree` (2 declarations, 2 files)

- `theorem Spartan.Spec.toMLE_evalC_mem_restrictDegree` [ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean:62](../../../ArkLib/ProofSystem/Spartan/SecondSumcheckReduction.lean#L62) — (no docstring)
- `theorem Spartan.toMLE_evalC_mem_restrictDegree` [ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean:54](../../../ArkLib/ProofSystem/Spartan/SumcheckDegreeBound.lean#L54) — **The row-fixed matrix MLE is multilinear in the column variables (degree ≤ 1).**

### `toMonadDecoration` (2 declarations, 2 files)

- `def Interaction.OracleDecoration.toMonadDecoration` [ArkLib/Interaction/Oracle/Core.lean:802](../../../ArkLib/Interaction/Oracle/Core.lean#L802) — (no docstring)
- `def Interaction.Oracle.Spec.toMonadDecoration` [ArkLib/Interaction/Oracle/Spec.lean:193](../../../ArkLib/Interaction/Oracle/Spec.lean#L193) — (no docstring)

### `toOracleSpec` (2 declarations, 2 files)

- `def Interaction.Oracle.Spec.toOracleSpec` [ArkLib/Interaction/Oracle/Spec.lean:158](../../../ArkLib/Interaction/Oracle/Spec.lean#L158) — (no docstring)
- `def OracleInterface.toOracleSpec` [ArkLib/OracleReduction/OracleInterface.lean:92](../../../ArkLib/OracleReduction/OracleInterface.lean#L92) — Converts an indexed type family of oracle interfaces into an oracle specification. Notation: `[v]ₒ`

### `toPoly` (2 declarations, 2 files)

- `def GSMultInterp.toPoly` [ArkLib/Data/CodingTheory/GuruswamiSudan/DictionaryBridge.lean:26](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/DictionaryBridge.lean#L26) — The bivariate polynomial `∑_{(s,t)∈monoIdx} c(s,t)·X^s·Y^t` carried by a coefficient vector `c`, as
- `def UniPoly.toPoly` [ArkLib/Data/UniPoly/Basic.lean:758](../../../ArkLib/Data/UniPoly/Basic.lean#L758) — Convert a `UniPoly` to a (mathlib) `Polynomial`.

### `toPoly_add` (2 declarations, 2 files)

- `theorem GSMultInterp.toPoly_add` [ArkLib/Data/CodingTheory/GuruswamiSudan/DictionaryBridge.lean:48](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/DictionaryBridge.lean#L48) — `toPoly` is additive in the coefficient vector.
- `theorem UniPoly.toPoly_add` [ArkLib/Data/UniPoly/Basic.lean:854](../../../ArkLib/Data/UniPoly/Basic.lean#L854) — `UniPoly` addition is mapped to `Polynomial` addition

### `two_ne_zero_zmod13` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.Round6MultCharacter.two_ne_zero_zmod13` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumE2PowerSumReduction.lean:339](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumE2PowerSumReduction.lean#L339) — **`(2 : F) ≠ 0` is realized in the smooth-domain regime (concrete witness `F = ZMod 13`).** The smoo
- `theorem ArkLib.CodingTheory.Round7PaleyZygmund.two_ne_zero_zmod13` [ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPaleyZygmundDichotomy.lean:384](../../../ArkLib/Data/CodingTheory/ProximityGap/SubsetSumPaleyZygmundDichotomy.lean#L384) — **`(2 : ZMod 13) ≠ 0` — the smooth-domain regime is realized.** The smooth `2^k`-subgroup lives in o

### `umCode` (2 declarations, 2 files)

- `def ReedSolomon.Multiplicity.umCode` [ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean:97](../../../ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean#L97) — **ABF26 Definition A.7 [GW13, KSY14]** — the univariate multiplicity code `UM[F, L, k, s]`. Defined
- `def CodingTheory.umCode` [ArkLib/Data/CodingTheory/SubspaceDesign.lean:1105](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean#L1105) — **ABF26 DA.7 (Univariate Multiplicity codes)**. The UM code `UM[F, L, k, s]`: `UM[F, L, k, s] := { f

### `uniform` (2 declarations, 2 files)

- `def OracleReduction.OracleDistribution.uniform` [ArkLib/OracleReduction/Security/OracleDistribution.lean:119](../../../ArkLib/OracleReduction/Security/OracleDistribution.lean#L119) — Uniform full-table sampling. Requires `SampleableType` over the dependent product `OracleFamily spec
- `def SumcheckDomain.uniform` [ArkLib/ProofSystem/Sumcheck/Domain.lean:74](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L74) — The *uniform* domain: the same `m`-point embedding `D₀` in every one of the `k` coordinates. Its `cu

### `unroll_2_message_VP` (2 declarations, 2 files)

- `theorem StirIOP.Round.unroll_2_message_VP` [ArkLib/ProofSystem/Stir/RoundCompleteness.lean:55](../../../ArkLib/ProofSystem/Stir/RoundCompleteness.lean#L55) — (no docstring)
- `theorem WhirIOP.FoldRound.unroll_2_message_VP` [ArkLib/ProofSystem/Whir/FoldRound.lean:65](../../../ArkLib/ProofSystem/Whir/FoldRound.lean#L65) — (no docstring)

### `urow0` (2 declarations, 2 files)

- `def ProximityGap.MCANearCapacityGK.urow0` [ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityGeneralRate.lean:121](../../../ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityGeneralRate.lean#L121) — First row `u₀ i = (domain i)ᵏ⁺¹`.
- `def ProximityGap.MCANearCapacity.urow0` [ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityLowerBound.lean:62](../../../ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityLowerBound.lean#L62) — First row `u₀ i = i²`.

### `urow1` (2 declarations, 2 files)

- `def ProximityGap.MCANearCapacityGK.urow1` [ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityGeneralRate.lean:123](../../../ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityGeneralRate.lean#L123) — Second row `u₁ i = (domain i)ᵏ`.
- `def ProximityGap.MCANearCapacity.urow1` [ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityLowerBound.lean:64](../../../ArkLib/Data/CodingTheory/ProximityGap/MCANearCapacityLowerBound.lean#L64) — Second row `u₁ i = i`.

### `vanishesToOrder` (2 declarations, 2 files)

- `def GSMultInterp.vanishesToOrder` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:153](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L153) — `Q` (given by coefficient vector `c`) **vanishes to order `m`** at `(x₀, y₀)`: every Hasse coefficie
- `def ArkLib.GS.vanishesToOrder` [ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean#L60) — `Q : F[X][Y]` **vanishes to order `m` at `(a, b)`** when, for every `Y`-index `j`, the inner Taylor

### `vanishing_sum_antipodal` (2 declarations, 2 files)

- `theorem LamLeungTwoPow.vanishing_sum_antipodal` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean:59](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean#L59) — **Lam–Leung at the prime 2** (the O48 tower base case): in characteristic zero, a finite set of `2^(
- `theorem Round29IteratedLift.vanishing_sum_antipodal` [ArkLib/Data/CodingTheory/ProximityGap/RigidityIterated2kLift.lean:561](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityIterated2kLift.lean#L561) — **Lam–Leung at `p = 2`, single-set form (the queued O47 brick, now a theorem):** in characteristic 0

### `vanishing_sum_mu_p_closed` (2 declarations, 2 files)

- `theorem LamLeungTwoPow.vanishing_sum_mu_p_closed` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean:1226](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean#L1226) — **Lam–Leung at prime powers**: in characteristic zero, a finite set of `p^(m+1)`-th roots of unity w
- `theorem MixedRadixTower.vanishing_sum_mu_p_closed` [ArkLib/Data/CodingTheory/ProximityGap/MixedRadixTower.lean:521](../../../ArkLib/Data/CodingTheory/ProximityGap/MixedRadixTower.lean#L521) — **Lam–Leung at prime powers**: in characteristic zero, a finite set of `p^(m+1)`-th roots of unity w

### `vecL2NormSq` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:91](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L91) — Centered squared-`ℓ₂` norm of a vector: the sum of entrywise norms.
- `def ArkLib.Lattices.CenteredCoeffView.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/Norms.lean:80](../../../ArkLib/Data/Lattices/CyclotomicRing/Norms.lean#L80) — Vector squared `ℓ₂` norm: the sum of entrywise squared `ℓ₂` norms.

### `verifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem DoNothing.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:58](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L58) — The `DoNothing` verifier is perfectly round-by-round knowledge sound.
- `theorem ReduceClaim.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:225](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L225) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s

### `verifyOpening` (2 declarations, 2 files)

- `def KZG.verifyOpening` [ArkLib/CommitmentScheme/KZG/Basic.lean:69](../../../ArkLib/CommitmentScheme/KZG/Basic.lean#L69) — To verify a KZG opening `opening` for a commitment `commitment` at point `z` with claimed evaluation
- `def InductiveMerkleTree.verifyOpening` [ArkLib/CommitmentScheme/MerkleTree/Batch.lean:101](../../../ArkLib/CommitmentScheme/MerkleTree/Batch.lean#L101) — Verify one packaged opening against a claimed root, in `OracleComp (spec α)`.

### `weight_Λ_over_𝒪_add_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_add_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:650](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L650) — `Λ_𝒪(a + b) ≤ max(Λ_𝒪 a, Λ_𝒪 b)`: sub-additivity over `𝒪 H`.
- `lemma ArkLib.weight_Λ_over_𝒪_add_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:82](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L82) — Sub-additivity of the `𝒪`-weight under addition: `Λ(a + b) ≤ max (Λ a) (Λ b)`.

### `weight_Λ_over_𝒪_mul_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_mul_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:635](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L635) — `Λ_𝒪(a · b) ≤ Λ_𝒪(a) + Λ_𝒪(b)`: sub-multiplicativity over `𝒪 H`.  Take the canonical representatives
- `lemma ArkLib.weight_Λ_over_𝒪_mul_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:143](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L143) — Sub-multiplicativity of the `𝒪`-weight: `Λ(a · b) ≤ Λ a + Λ b`. This is the central inequality the A

### `weight_Λ_over_𝒪_neg` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_neg` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:665](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L665) — `Λ_𝒪(-a) = Λ_𝒪(a)`: the `𝒪`-weight is negation-invariant (`mk (-ra) = -a`, `weight_Λ_neg`).
- `lemma ArkLib.weight_Λ_over_𝒪_neg` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:99](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L99) — Sub-additivity of the `𝒪`-weight under negation: it is invariant.

### `weight_Λ_over_𝒪_pow_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_pow_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:691](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L691) — `Λ_𝒪(a ^ k) ≤ k • Λ_𝒪(a)` (i.e. `≤ k · Λ_𝒪(a)` in `WithBot ℕ`): the power bound over `𝒪 H`, by induc
- `lemma ArkLib.weight_Λ_over_𝒪_pow_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:158](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L158) — Sub-multiplicativity for powers: `Λ(a ^ n) ≤ n • Λ a` (with `0 • Λ a = 0`, matching `weight_Λ_over_𝒪

### `weight_Λ_over_𝒪_sum_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_sum_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:677](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L677) — `Λ_𝒪(∑ᵢ f i) ≤ sup of Λ_𝒪(f i)`: the `𝒪`-weight of a finite sum is bounded by the sup of the summand
- `lemma ArkLib.weight_Λ_over_𝒪_sum_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:124](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L124) — The `𝒪`-weight of a finite sum is bounded by the `sup` of the summands' weights.

### `whirCheckedVectorIOP_isSecureWithGap_of_rbr` (2 declarations, 2 files)

- `theorem Whir302Checked.whirCheckedVectorIOP_isSecureWithGap_of_rbr` [ArkLib/ProofSystem/Whir/CheckedVerifier.lean:1006](../../../ArkLib/ProofSystem/Whir/CheckedVerifier.lean#L1006) — With the completeness leg PROVEN for the checking verifier, `IsSecureWithGap` for the checked WHIR `
- `theorem WhirIOP.whirCheckedVectorIOP_isSecureWithGap_of_rbr` [ArkLib/ProofSystem/Whir/ProtocolSoundness.lean:202](../../../ArkLib/ProofSystem/Whir/ProtocolSoundness.lean#L202) — The checked WHIR `VectorIOP` has the secure-with-gap package once its genuine RBR knowledge-soundnes

### `whirVectorIOP_isSecureWithGap_indicator` (2 declarations, 2 files)

- `theorem WhirIOP.whirVectorIOP_isSecureWithGap_indicator` [ArkLib/ProofSystem/Whir/ProtocolSoundness.lean:161](../../../ArkLib/ProofSystem/Whir/ProtocolSoundness.lean#L161) — Secure-with-gap package for the current WHIR skeleton at the proved indicator budget.
- `theorem Whir302RBR.whirVectorIOP_isSecureWithGap_indicator` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:478](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L478) — **The full security package with the indicator budget:** the concrete WHIR `VectorIOP` is secure wit

### `whirVectorIOP_perfectCompleteness_holds` (2 declarations, 2 files)

- `theorem Whir302.whirVectorIOP_perfectCompleteness_holds` [ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean:125](../../../ArkLib/ProofSystem/Whir/ProtocolCompleteness.lean#L125) — (no docstring)
- `theorem Whir302RBR.whirVectorIOP_perfectCompleteness_holds` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:469](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L469) — The perfect-completeness residual of the concrete WHIR `VectorIOP` (replica of `Whir302.whirVectorIO

### `whirVectorIOP_rbrKnowledgeSoundness_indicator` (2 declarations, 2 files)

- `theorem WhirIOP.whirVectorIOP_rbrKnowledgeSoundness_indicator` [ArkLib/ProofSystem/Whir/ProtocolSoundness.lean:101](../../../ArkLib/ProofSystem/Whir/ProtocolSoundness.lean#L101) — **Proved indicator-budget RBR package for the current WHIR skeleton.**  The state-function argument
- `theorem Whir302RBR.whirVectorIOP_rbrKnowledgeSoundness_indicator` [ArkLib/ProofSystem/Whir/ThresholdKSF.lean:335](../../../ArkLib/ProofSystem/Whir/ThresholdKSF.lean#L335) — **Discharged #302 residual (indicator budget):** the concrete WHIR `VectorIOP` satisfies round-by-ro

### `window_halving_step` (2 declarations, 2 files)

- `theorem Round28FullWindow.window_halving_step` [ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean:163](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityFullWindow.lean#L163) — **THE WINDOW-HALVING STEP (the full-window recursion engine).** Let `A, B` be antipodally closed (su
- `theorem Round26Recursion.window_halving_step` [ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean:161](../../../ArkLib/Data/CodingTheory/ProximityGap/RigidityWindowHalving.lean#L161) — **THE WINDOW-HALVING STEP (the full-window recursion engine).** Let `A, B` be antipodally closed (su

### `witnessStructuralInvariant` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1441](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1441) — This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
- `def RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:492](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L492) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`

### `witness_list_card_seven` (2 declarations, 2 files)

- `theorem ArkLib.CodingTheory.TinyInteriorK3.witness_list_card_seven` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:168](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L168) — **The list has exactly seven elements.** All seven explicit codewords are pairwise distinct.
- `theorem ArkLib.CodingTheory.Round3SmoothF17.witness_list_card_seven` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean:177](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF17Subgroup.lean#L177) — **The list has exactly seven elements.** All seven explicit smooth-domain codewords are pairwise dis

### `AnchoredFrom` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.AnchoredFrom` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:78](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L78) — Some entry of the log is an anchored collision against the running cache.
- `def DuplexSpongeFS.EagerLazyDS.AnchoredFrom` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:78](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L78) — Some entry of the log is an anchored collision against the running cache.

### `ConsistentFrom` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.ConsistentFrom` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:73](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L73) — The whole log is consistent with the running cache.
- `def DuplexSpongeFS.EagerLazyDS.ConsistentFrom` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:73](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L73) — The whole log is consistent with the running cache.

### `DSEntry` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.EagerLazyDS.DSEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L46) — A single log entry of the combined oracle.
- `abbrev DuplexSpongeFS.EagerLazyDS.DSEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L46) — A single log entry of the combined oracle.

### `EPaperReduction` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.EagerLazyDS.EPaperReduction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1598](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1598) — The dedup reduction (the one remaining pure-combinatorics obligation): a log consistent with the emp
- `abbrev DuplexSpongeFS.EagerLazyDS.EPaperReduction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1598](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1598) — The dedup reduction (the one remaining pure-combinatorics obligation): a log consistent with the emp

### `E_of_base_hasForwardCapacityBeforeForwardOutput` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.E_of_base_hasForwardCapacityBeforeForwardOutput` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1131](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1131) — If the deduplicated trace has the broader base permutation-ordering capacity shape, the combined bad
- `theorem DuplexSpongeFS.Sponge316.E_of_base_hasForwardCapacityBeforeForwardOutput` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1131](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1131) — If the deduplicated trace has the broader base permutation-ordering capacity shape, the combined bad

### `E_of_base_hasForwardCapacityBeforeHash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.E_of_base_hasForwardCapacityBeforeHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1103](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1103) — Predicate form of `E_of_base_hash_after_forward_capacity`: once the deduplicated base trace has the
- `theorem DuplexSpongeFS.Sponge316.E_of_base_hasForwardCapacityBeforeHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1103](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1103) — Predicate form of `E_of_base_hash_after_forward_capacity`: once the deduplicated base trace has the

### `E_of_base_hasInputCapacityBeforeForwardOutput` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.E_of_base_hasInputCapacityBeforeForwardOutput` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1115](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1115) — If the deduplicated trace has the base permutation-ordering capacity shape, the combined bad event f
- `theorem DuplexSpongeFS.Sponge316.E_of_base_hasInputCapacityBeforeForwardOutput` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1115](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1115) — If the deduplicated trace has the base permutation-ordering capacity shape, the combined bad event f

### `E_of_base_hash_after_forward_capacity` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.E_of_base_hash_after_forward_capacity` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1078](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1078) — If the deduplicated trace has a hash entry and a strictly earlier forward permutation entry sharing
- `theorem DuplexSpongeFS.Sponge316.E_of_base_hash_after_forward_capacity` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1078](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1078) — If the deduplicated trace has a hash entry and a strictly earlier forward permutation entry sharing

### `E_of_hasFirstHashForwardCapacityBeforeHash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.E_of_hasFirstHashForwardCapacityBeforeHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:220](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L220) — Raw first-occurrence collision shape fires the combined bad event `E`: transport the shape through d
- `theorem DuplexSpongeFS.Sponge316.E_of_hasFirstHashForwardCapacityBeforeHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:220](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L220) — Raw first-occurrence collision shape fires the combined bad event `E`: transport the shape through d

### `FwdKeysNodup` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.FwdKeysNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:661](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L661) — The forward keys of the permutation cache are distinct.
- `def DuplexSpongeFS.EagerLazyDS.FwdKeysNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:661](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L661) — The forward keys of the permutation cache are distinct.

### `H_dvd_radical_fiber` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.H_dvd_radical_fiber` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:78](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L78) — **`H` divides the radical of the fiber**: irreducibility + `dvd_evalX` + nonzeroness — no separabili
- `theorem ArkLib.RadicalWire304.H_dvd_radical_fiber` [ArkLib/ToMathlib/RadicalAssembler.lean:97](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L97) — **`H` divides the radical of the fiber**: irreducibility + `dvd_evalX` + nonzeroness — no separabili

### `H_eval_centreFold_eq_zero` (2 declarations, 2 files)

- `theorem ArkLib.XiCertReduction.H_eval_centreFold_eq_zero` [ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean:94](../../../ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean#L94) — **The centre fold globally roots `H`**: through the GS split `evalX (C x₀) R = H·G` and the global b
- `theorem ArkLib.XiCertReduction.H_eval_centreFold_eq_zero` [ArkLib/ToMathlib/XiCertReduction.lean:125](../../../ArkLib/ToMathlib/XiCertReduction.lean#L125) — **The centre fold globally roots `H`**: through the GS split `evalX (C x₀) R = H·G` and the global b

### `H_eval_centreFold_eq_zero_radical` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.H_eval_centreFold_eq_zero_radical` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:346](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L346) — **The centre fold globally roots `H`, through the RADICAL**: mirror of `XiCertReduction.H_eval_centr
- `theorem ArkLib.RadicalWire304.H_eval_centreFold_eq_zero_radical` [ArkLib/ToMathlib/RadicalAssembler.lean:365](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L365) — **The centre fold globally roots `H`, through the RADICAL**: mirror of `XiCertReduction.H_eval_centr

### `H_matrix` (2 declarations, 2 files)

- `def H_matrix` [ArkLib/Data/CodingTheory/ProximityGap/PromotedHypothesesB.lean:23](../../../ArkLib/Data/CodingTheory/ProximityGap/PromotedHypothesesB.lean#L23) — (no docstring)
- `def H_matrix` [ArkLib/Data/CodingTheory/Quarantine/HypothesesRefutations.lean:22](../../../ArkLib/Data/CodingTheory/Quarantine/HypothesesRefutations.lean#L22) — (no docstring)

### `HasCapBeforeInverseAnswerPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:126](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L126) — Broad (guard-free) inverse-anchored collision shape, for the dedup'd base trace.
- `def DuplexSpongeFS.Sponge316.HasCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:126](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L126) — Broad (guard-free) inverse-anchored collision shape, for the dedup'd base trace.

### `HasFirstCapBeforeInverseAnswerPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:116](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L116) — First-occurrence inverse-anchored collision shape (paper semantics, ℕ-indexed): an inverse entry wit
- `def DuplexSpongeFS.Sponge316.HasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:116](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L116) — First-occurrence inverse-anchored collision shape (paper semantics, ℕ-indexed): an inverse entry wit

### `HasFirstForwardCapacityBeforeForwardOutput` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstForwardCapacityBeforeForwardOutput` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:540](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L540) — Strengthened permutation-ordering collision shape: the later forward permutation entry is the first
- `def DuplexSpongeFS.Sponge316.HasFirstForwardCapacityBeforeForwardOutput` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:540](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L540) — Strengthened permutation-ordering collision shape: the later forward permutation entry is the first

### `HasFirstForwardCapacityBeforeForwardOutputNat` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstForwardCapacityBeforeForwardOutputNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:598](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L598) — Natural-index form of `HasFirstForwardCapacityBeforeForwardOutput`, used for the recursive `eraseIdx
- `def DuplexSpongeFS.Sponge316.HasFirstForwardCapacityBeforeForwardOutputNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:598](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L598) — Natural-index form of `HasFirstForwardCapacityBeforeForwardOutput`, used for the recursive `eraseIdx

### `HasFirstHashForwardCapacityBeforeHash` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstHashForwardCapacityBeforeHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:173](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L173) — Strengthened raw collision shape: the hash entry is the first occurrence of its concrete hash anchor
- `def DuplexSpongeFS.Sponge316.HasFirstHashForwardCapacityBeforeHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:173](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L173) — Strengthened raw collision shape: the hash entry is the first occurrence of its concrete hash anchor

### `HasFirstHashForwardCapacityBeforeHashNat` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstHashForwardCapacityBeforeHashNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:349](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L349) — Natural-index form of `HasFirstHashForwardCapacityBeforeHash`, used for the recursive `eraseIdx` pro
- `def DuplexSpongeFS.Sponge316.HasFirstHashForwardCapacityBeforeHashNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:349](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L349) — Natural-index form of `HasFirstHashForwardCapacityBeforeHash`, used for the recursive `eraseIdx` pro

### `HasFirstHashFwdCapNat` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstHashFwdCapNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:55](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L55) — ℕ-indexed, `getElem?`-based restatement of `HasFirstHashForwardCapacityBeforeHash`: a first-occurren
- `def DuplexSpongeFS.Sponge316.HasFirstHashFwdCapNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:55](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L55) — ℕ-indexed, `getElem?`-based restatement of `HasFirstHashForwardCapacityBeforeHash`: a first-occurren

### `HasFirstHashPermCapNatPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:707](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L707) — ℕ-indexed first-hash collision shape, paper semantics: the hash anchor is first-occurrence, and an e
- `def DuplexSpongeFS.Sponge316.HasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:707](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L707) — ℕ-indexed first-hash collision shape, paper semantics: the hash anchor is first-occurrence, and an e

### `HasFirstPermCapacityBeforeForwardOutputPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:271](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L271) — Paper-semantics first-occurrence collision shape: the tracked forward entry has no prior copy of its
- `def DuplexSpongeFS.Sponge316.HasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:271](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L271) — Paper-semantics first-occurrence collision shape: the tracked forward entry has no prior copy of its

### `HasFirstPermCapacityBeforeForwardOutputPaperNat` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasFirstPermCapacityBeforeForwardOutputPaperNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:331](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L331) — Natural-index form of `HasFirstPermCapacityBeforeForwardOutputPaper`, for the recursive `eraseIdx` p
- `def DuplexSpongeFS.Sponge316.HasFirstPermCapacityBeforeForwardOutputPaperNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:331](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L331) — Natural-index form of `HasFirstPermCapacityBeforeForwardOutputPaper`, for the recursive `eraseIdx` p

### `HasForwardCapacityBeforeForwardOutput` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasForwardCapacityBeforeForwardOutput` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:146](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L146) — The trace contains a forward permutation entry whose output capacity matches either side of a strict
- `def DuplexSpongeFS.Sponge316.HasForwardCapacityBeforeForwardOutput` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:146](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L146) — The trace contains a forward permutation entry whose output capacity matches either side of a strict

### `HasForwardCapacityBeforeHash` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasForwardCapacityBeforeHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:111](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L111) — The trace contains a hash entry with a strictly earlier forward permutation entry sharing the hash c
- `def DuplexSpongeFS.Sponge316.HasForwardCapacityBeforeHash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:111](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L111) — The trace contains a hash entry with a strictly earlier forward permutation entry sharing the hash c

### `HasHashEntry` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasHashEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:102](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L102) — The trace contains a concrete hash entry.
- `def DuplexSpongeFS.Sponge316.HasHashEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:102](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L102) — The trace contains a concrete hash entry.

### `HasHashPermCapBeforeHashPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasHashPermCapBeforeHashPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:719](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L719) — Broad (no-firstness) hash-anchored collision shape, paper semantics.
- `def DuplexSpongeFS.Sponge316.HasHashPermCapBeforeHashPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:719](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L719) — Broad (no-firstness) hash-anchored collision shape, paper semantics.

### `HasInputCapacityBeforeForwardOutput` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasInputCapacityBeforeForwardOutput` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:128](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L128) — The trace contains a forward permutation entry whose output capacity matches the input capacity of a
- `def DuplexSpongeFS.Sponge316.HasInputCapacityBeforeForwardOutput` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:128](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L128) — The trace contains a forward permutation entry whose output capacity matches the input capacity of a

### `HasInvEntry` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasInvEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:47](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L47) — The trace contains an inverse-permutation (`p⁻¹`) entry.
- `def DuplexSpongeFS.Sponge316.HasInvEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:47](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L47) — The trace contains an inverse-permutation (`p⁻¹`) entry.

### `HasPermCapacityBeforeForwardOutputPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:256](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L256) — Direction-agnostic prior-permutation capacity shape: some permutation entry (either direction) stric
- `def DuplexSpongeFS.Sponge316.HasPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:256](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L256) — Direction-agnostic prior-permutation capacity shape: some permutation entry (either direction) stric

### `HasPriorReversedForwardAnchor` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasPriorReversedForwardAnchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1446](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1446) — A raw obstruction to the first-forward transport guard: a `J_BT` permutation anchor has a strictly e
- `def DuplexSpongeFS.Sponge316.HasPriorReversedForwardAnchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1446](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1446) — A raw obstruction to the first-forward transport guard: a `J_BT` permutation anchor has a strictly e

### `HasRedundantForwardAnchor` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.HasRedundantForwardAnchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1458](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1458) — A `J_BT` nonterminal forward anchor is redundant under the in-tree `redundantEntryDS` predicate. Off
- `def DuplexSpongeFS.Sponge316.HasRedundantForwardAnchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1458](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1458) — A `J_BT` nonterminal forward anchor is redundant under the in-tree `redundantEntryDS` predicate. Off

### `Lemma5_12HonestResidualPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.Lemma5_12HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:658](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L658) — CO25 Lemma 5.12 (honest form), **paper semantics**: off the paper combined bad event, no BackTrack c
- `def DuplexSpongeFS.Sponge316.Lemma5_12HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:658](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L658) — CO25 Lemma 5.12 (honest form), **paper semantics**: off the paper combined bad event, no BackTrack c

### `Lemma5_14HonestResidualPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.Lemma5_14HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:666](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L666) — CO25 Lemma 5.14 (honest form), **paper semantics**: off the paper combined bad event, the backtrack
- `def DuplexSpongeFS.Sponge316.Lemma5_14HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:666](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L666) — CO25 Lemma 5.14 (honest form), **paper semantics**: off the paper combined bad event, the backtrack

### `Lemma5_16HonestResidualPaper` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.Lemma5_16HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:676](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L676) — CO25 Lemma 5.16 (honest form), **paper semantics**: off the paper combined bad event, all chain quer
- `def DuplexSpongeFS.Sponge316.Lemma5_16HonestResidualPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:676](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L676) — CO25 Lemma 5.16 (honest form), **paper semantics**: off the paper combined bad event, all chain quer

### `OracleInterface` (3 declarations, 2 files)

- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:88](../../../ArkLib/OracleReduction/Basic.lean#L88) — (no docstring)
- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:162](../../../ArkLib/OracleReduction/Basic.lean#L162) — (no docstring)
- `class OracleInterface` [ArkLib/OracleReduction/OracleInterface.lean:52](../../../ArkLib/OracleReduction/OracleInterface.lean#L52) — `OracleInterface` is a type class that provides an oracle interface for a type `Message`. It consist

### `Section5StrictDataFinOn.ofProducersOn` (2 declarations, 2 files)

- `def ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn` [ArkLib/ToMathlib/BCIKS20BundleAssembler.lean:140](../../../ArkLib/ToMathlib/BCIKS20BundleAssembler.lean#L140) — **The satisfiable-bundle producer assembly** — the restricted (`rootOn`/`mpFinOn`) mirror of `Keysto
- `def ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn` [ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean:217](../../../ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean#L217) — **The satisfiable-bundle producer assembly** — the restricted (`rootOn`/`mpFinOn`) mirror of `Keysto

### `Section5StrictDataFinOn.ofProducersOn_gradedSigned` (2 declarations, 2 files)

- `def ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn_gradedSigned` [ArkLib/ToMathlib/BCIKS20BundleAssembler.lean:286](../../../ArkLib/ToMathlib/BCIKS20BundleAssembler.lean#L286) — **Producer assembly at the signed canonical family with the PROVEN graded weight chain** (monic case
- `def ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn_gradedSigned` [ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean:275](../../../ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean#L275) — **Producer assembly at the signed canonical family with the PROVEN graded weight chain** (monic case

### `Section5StrictDataFinOn.ofProducersOn_radical` (2 declarations, 2 files)

- `def ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn_radical` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:530](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L530) — **The satisfiable bundle from the RADICAL of the fiber** (monic case): mirror of `Section5StrictData
- `def ArkLib.RootOn304.Section5StrictDataFinOn.ofProducersOn_radical` [ArkLib/ToMathlib/RadicalAssembler.lean:549](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L549) — **The satisfiable bundle from the RADICAL of the fiber** (monic case): mirror of `Section5StrictData

### `SlotKind` (2 declarations, 2 files)

- `inductive DuplexSpongeFS.Sponge316.SlotKind` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:66](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L66) — A tagged trace slot: either a hash entry or a forward permutation entry. The tag determines the slot
- `inductive DuplexSpongeFS.Sponge316.SlotKind` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:66](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L66) — A tagged trace slot: either a hash entry or a forward permutation entry. The tag determines the slot

### `SlotKind.entry` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.SlotKind.entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:70](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L70) — (no docstring)
- `def DuplexSpongeFS.Sponge316.SlotKind.entry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:70](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L70) — (no docstring)

### `SlotKind.guard` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.SlotKind.guard` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:78](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L78) — The slot's first-occurrence guard: no strictly earlier slot holds any certificate target for this en
- `def DuplexSpongeFS.Sponge316.SlotKind.guard` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:78](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L78) — The slot's first-occurrence guard: no strictly earlier slot holds any certificate target for this en

### `SlotKind.not_redundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.SlotKind.not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:93](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L93) — A guarded slot is never paper-redundant.
- `lemma DuplexSpongeFS.Sponge316.SlotKind.not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:93](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L93) — A guarded slot is never paper-redundant.

### `SlotKind.ok` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.SlotKind.ok` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:88](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L88) — A guarded slot: the entry sits at slot `i` and is the first occurrence of its certificate class.
- `def DuplexSpongeFS.Sponge316.SlotKind.ok` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:88](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L88) — A guarded slot: the entry sits at slot `i` and is the first occurrence of its certificate class.

### `SlotKind.ok_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.SlotKind.ok_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:148](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L148) — A guarded slot shifts through `eraseIdx` of a different index.
- `lemma DuplexSpongeFS.Sponge316.SlotKind.ok_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:148](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L148) — A guarded slot shifts through `eraseIdx` of a different index.

### `TwoSurvivors` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TwoSurvivors` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:164](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L164) — Two ordered guarded slots, the raw-trace shape of the two-survivor transport.
- `def DuplexSpongeFS.Sponge316.TwoSurvivors` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:164](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L164) — Two ordered guarded slots, the raw-trace shape of the two-survivor transport.

### `aligned_inputs` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.aligned_inputs` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:191](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L191) — **End-aligned input agreement** (CO25 Claim 5.19, Eq. 44 induction): off `EPaper`, the input states
- `theorem DuplexSpongeFS.Paper.aligned_inputs` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:191](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L191) — **End-aligned input agreement** (CO25 Claim 5.19, Eq. 44 induction): off `EPaper`, the input states

### `aligned_inputs_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.aligned_inputs_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:546](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L546) — End-aligned input agreement: off `BadEventDSPaper.E`, two family sequences agree at end-aligned inpu
- `theorem DuplexSpongeFS.Sponge316.aligned_inputs_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:546](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L546) — End-aligned input agreement: off `BadEventDSPaper.E`, two family sequences agree at end-aligned inpu

### `alpha12_injective` (2 declarations, 2 files)

- `lemma R15.alpha12_injective` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:388](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L388) — Injectivity of the evaluation points `0, 1, …, 11` in `ZMod 13`.
- `lemma R15.alpha12_injective` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:388](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L388) — Injectivity of the evaluation points `0, 1, …, 11` in `ZMod 13`.

### `anchoredFrom_of_at` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_at` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:70](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L70) — **Positional anchoring**: a `collisionStep` at any position (against the prefix fold) yields `Anchor
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_at` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:70](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L70) — **Positional anchoring**: a `collisionStep` at any position (against the prefix fold) yields `Anchor

### `anchoredFrom_of_eraseIdx_classRed` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_eraseIdx_classRed` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:537](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L537) — A class-redundant erasure reflects anchoredness in a consistent log.
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_eraseIdx_classRed` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:537](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L537) — A class-redundant erasure reflects anchoredness in a consistent log.

### `anchoredFrom_of_eraseIdx_of_noop` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_eraseIdx_of_noop` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:375](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L375) — Erasing a no-op entry reflects anchoredness: a collision in the erased log is a collision in the ori
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_eraseIdx_of_noop` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:375](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L375) — Erasing a no-op entry reflects anchoredness: a collision in the erased log is a collision in the ori

### `anchoredFrom_of_removeRedundantEntryDSPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:595](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L595) — Anchoredness of the paper-deduplicated log reflects back to the original consistent log.
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:595](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L595) — Anchoredness of the paper-deduplicated log reflects back to the original consistent log.

### `anchoredFrom_of_removeRedundantEntryDSPaper_aux` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_removeRedundantEntryDSPaper_aux` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:557](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L557) — (no docstring)
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_removeRedundantEntryDSPaper_aux` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:557](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L557) — (no docstring)

### `anchoredFrom_of_split` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1084](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1084) — **Constructive anchoring**: a collision at a split point makes the whole fold anchored.
- `theorem DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1084](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1084) — **Constructive anchoring**: a collision at a split point makes the whole fold anchored.

### `anchored_of_E_func` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_func` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1569](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1569) — **E_func arm.** A function violation among dedup entries is impossible in a non-anchored consistent
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_func` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1569](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1569) — **E_func arm.** A function violation among dedup entries is impossible in a non-anchored consistent

### `anchored_of_E_h` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_h` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1464](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1464) — **E_h arm.** A hash-capacity duplicate among dedup entries anchors the consistent log.
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_h` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1464](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1464) — **E_h arm.** A hash-capacity duplicate among dedup entries anchors the consistent log.

### `anchored_of_E_p` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1491](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1491) — **E_p arm.** A forward-permutation capacity duplicate anchors the consistent log.
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_p` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1491](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1491) — **E_p arm.** A forward-permutation capacity duplicate anchors the consistent log.

### `anchored_of_E_pinv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1530](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1530) — **E_pinv arm.** An inverse-permutation capacity duplicate (B1-repaired) anchors the log.
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_E_pinv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1530](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1530) — **E_pinv arm.** An inverse-permutation capacity duplicate (B1-repaired) anchors the log.

### `anchored_of_hash_anchor` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_hash_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:299](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L299) — **The `E_hash` arm anchors a collision** (CO25 Eq. 24 over a certified consistent list): a hash entr
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_hash_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:299](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L299) — **The `E_hash` arm anchors a collision** (CO25 Eq. 24 over a certified consistent list): a hash entr

### `anchored_of_permInv_anchor` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_permInv_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:190](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L190) — **The `E_pinv` arm anchors a collision** (CO25 Eq. 26 over a certified consistent list): an inverse
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_permInv_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:190](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L190) — **The `E_pinv` arm anchors a collision** (CO25 Eq. 26 over a certified consistent list): an inverse

### `anchored_of_perm_anchor` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_perm_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:387](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L387) — **The `E_p` arm anchors a collision** (CO25 Eq. 25 over a certified consistent list): a forward entr
- `theorem DuplexSpongeFS.EagerLazyDS.anchored_of_perm_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:387](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L387) — **The `E_p` arm anchors a collision** (CO25 Eq. 25 over a certified consistent list): a forward entr

### `appendStage1Bridge` (2 declarations, 2 files)

- `theorem Reduction.appendStage1Bridge` [ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean:99](../../../ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean#L99) — **The discharged `hStage1Bridge`.** The `Prod.fst`-marginal of the state-threaded phase-1 stage game
- `theorem Reduction.appendStage1Bridge` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean:64](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean#L64) — **Discharged `hStage1Bridge`.** The `Prod.fst`-marginal of the state-threaded phase-1 stage game (`a

### `appendStage2Bridge` (2 declarations, 2 files)

- `theorem Reduction.appendStage2Bridge` [ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean:127](../../../ArkLib/OracleReduction/Composition/Sequential/AppendCompletenessMsgKeystone.lean#L127) — **The discharged `hStage2Bridge`.** For a phase-1 success `a` (with the completeness agreement `a.1.
- `theorem Reduction.appendStage2Bridge` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean:143](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges3.lean#L143) — **Discharged `hStage2Bridge`.** For each phase-1 success `a` with `goodOf rel₂ a` (which supplies th

### `appendStage₁_run_eq_liftM` (2 declarations, 2 files)

- `theorem Reduction.appendStage₁_run_eq_liftM` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean:171](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges.lean#L171) — **The `OptionT.run` of the phase-1 stage body equals `liftM` of `R₁.run`'s `OptionT.run`.** `appendS
- `theorem Reduction.appendStage₁_run_eq_liftM` [ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges2.lean:145](../../../ArkLib/OracleReduction/Composition/Sequential/AppendSeamBridges2.lean#L145) — **The `OptionT.run` of the phase-1 stage body equals `liftM` of `R₁.run`'s `OptionT.run`.** `appendS

### `base_earlier_fwd_slots` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_fwd_slots` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1328](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1328) — **Slot-persistence (forward).** An earlier forward base entry's pair is cached in the later entry's
- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_fwd_slots` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1328](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1328) — **Slot-persistence (forward).** An earlier forward base entry's pair is cached in the later entry's

### `base_earlier_hash_slot` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_hash_slot` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1426](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1426) — **Slot-persistence (hash).**
- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_hash_slot` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1426](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1426) — **Slot-persistence (hash).**

### `base_earlier_inv_slots` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_inv_slots` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1390](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1390) — **Slot-persistence (inverse).**
- `theorem DuplexSpongeFS.EagerLazyDS.base_earlier_inv_slots` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1390](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1390) — **Slot-persistence (inverse).**

### `base_fwd_anchored` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_fwd_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1117](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1117) — **Forward-arm anchoring producer.** If a forward base entry `⟨inr (inl a), b⟩` has its answer capaci
- `theorem DuplexSpongeFS.EagerLazyDS.base_fwd_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1117](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1117) — **Forward-arm anchoring producer.** If a forward base entry `⟨inr (inl a), b⟩` has its answer capaci

### `base_hash_anchored` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_hash_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1240](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1240) — **Hash-arm anchoring producer.** A hash base entry whose answer is an existing slot anchors the cons
- `theorem DuplexSpongeFS.EagerLazyDS.base_hash_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1240](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1240) — **Hash-arm anchoring producer.** A hash base entry whose answer is an existing slot anchors the cons

### `base_inv_anchored` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_inv_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1152](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1152) — **Inverse-arm anchoring producer.** Symmetric to `base_fwd_anchored` for an inverse base entry `⟨inr
- `theorem DuplexSpongeFS.EagerLazyDS.base_inv_anchored` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1152](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1152) — **Inverse-arm anchoring producer.** Symmetric to `base_fwd_anchored` for an inverse base entry `⟨inr

### `base_no_earlier_sameClass` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_no_earlier_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1064](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1064) — **w1**: a base entry has no earlier same-class entry in its raw prefix. Directly from the first-occu
- `theorem DuplexSpongeFS.EagerLazyDS.base_no_earlier_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1064](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1064) — **w1**: a base entry has no earlier same-class entry in its raw prefix. Directly from the first-occu

### `base_raw_split` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.base_raw_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:905](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L905) — **Raw split at a base position.** For a base-trace index `j`, writing `pⱼ = f j` for the order embed
- `theorem DuplexSpongeFS.EagerLazyDS.base_raw_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:905](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L905) — **Raw split at a base position.** For a base-trace index `j`, writing `pⱼ = f j` for the order embed

### `cacheFold_hash_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.cacheFold_hash_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:148](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L148) — Every cached hash answer in a fold of `ℓ` over `c₀` either was in `c₀` or comes from a hash entry of
- `theorem DuplexSpongeFS.EagerLazyDS.cacheFold_hash_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:148](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L148) — Every cached hash answer in a fold of `ℓ` over `c₀` either was in `c₀` or comes from a hash entry of

### `cacheFold_pair_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.cacheFold_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:190](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L190) — Every cached permutation pair in a fold of `ℓ` over `c₀` either was in `c₀` or comes from a forward
- `theorem DuplexSpongeFS.EagerLazyDS.cacheFold_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:190](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L190) — Every cached permutation pair in a fold of `ℓ` over `c₀` either was in `c₀` or comes from a forward

### `cannot` (2 declarations, 2 files)

- `class cannot` [ArkLib/Data/CodingTheory/ProximityGap/Jo26MissingLineSmallSeed.lean:34](../../../ArkLib/Data/CodingTheory/ProximityGap/Jo26MissingLineSmallSeed.lean#L34) — (no docstring)
- `structure cannot` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorQDependenceNoGo.lean:69](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorQDependenceNoGo.lean#L69) — (no docstring)

### `capacitySegmentDupPermInv_of_inv_mem` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.capacitySegmentDupPermInv_of_inv_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:915](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L915) — Any inverse-permutation entry in the dedup'd trace fires `E_pinv` (`capacitySegmentDupPermInv`): the
- `lemma DuplexSpongeFS.Sponge316.capacitySegmentDupPermInv_of_inv_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:915](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L915) — Any inverse-permutation entry in the dedup'd trace fires `E_pinv` (`capacitySegmentDupPermInv`): the

### `card_capacityFiber_preimage` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.card_capacityFiber_preimage` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:139](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L139) — The capacity-fiber preimage count: exactly `\|W\| · \|U\|^R` states carry a capacity from `W`.
- `lemma DuplexSpongeFS.EagerLazyDS.card_capacityFiber_preimage` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:139](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L139) — The capacity-fiber preimage count: exactly `\|W\| · \|U\|^R` states carry a capacity from `W`.

### `card_le_of_unusedKeysList_eq_nil` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.card_le_of_unusedKeysList_eq_nil` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:229](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L229) — An exhausted keys pool forces the cache to cover the type.
- `lemma DuplexSpongeFS.EagerLazyDS.card_le_of_unusedKeysList_eq_nil` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:229](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L229) — An exhausted keys pool forces the cache to cover the type.

### `card_le_of_unusedValuesList_eq_nil` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.card_le_of_unusedValuesList_eq_nil` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:220](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L220) — An exhausted values pool forces the cache to cover the type.
- `lemma DuplexSpongeFS.EagerLazyDS.card_le_of_unusedValuesList_eq_nil` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:220](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L220) — An exhausted values pool forces the cache to cover the type.

### `card_listEval_eq_le` (2 declarations, 2 files)

- `theorem Whir302SZ.card_listEval_eq_le` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:64](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L64) — **The Schwartz–Zippel salvage bound for `listEval`** (the WHIR sumcheck flip event): if two coeffici
- `theorem Whir302SZ.card_listEval_eq_le` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:137](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L137) — **The Schwartz–Zippel salvage bound for `listEval`** (the WHIR sumcheck flip event): if two coeffici

### `centreFold_dvd_radical` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.centreFold_dvd_radical` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:281](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L281) — The centre-fold linear factor divides the RADICAL of the fiber (monic linear is prime, hence irreduc
- `theorem ArkLib.RadicalWire304.centreFold_dvd_radical` [ArkLib/ToMathlib/RadicalAssembler.lean:300](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L300) — The centre-fold linear factor divides the RADICAL of the fiber (monic linear is prime, hence irreduc

### `cert_radical_dvd_cert_fiber` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.cert_radical_dvd_cert_fiber` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:238](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L238) — The radical branch certificate divides the fiber branch certificate.
- `theorem ArkLib.RadicalWire304.cert_radical_dvd_cert_fiber` [ArkLib/ToMathlib/RadicalAssembler.lean:257](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L257) — The radical branch certificate divides the fiber branch certificate.

### `cert_radical_natDegree_le` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.cert_radical_natDegree_le` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:191](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L191) — **The radical branch-certificate degree budget**: with coefficient bounds `DX` on the canonical radi
- `theorem ArkLib.RadicalWire304.cert_radical_natDegree_le` [ArkLib/ToMathlib/RadicalAssembler.lean:210](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L210) — **The radical branch-certificate degree budget**: with coefficient bounds `DX` on the canonical radi

### `choose_pow_le_qEntropy` (2 declarations, 2 files)

- `theorem CodingTheory.choose_pow_le_qEntropy` [ArkLib/Data/CodingTheory/EntropyVolumeUpper.lean:55](../../../ArkLib/Data/CodingTheory/EntropyVolumeUpper.lean#L55) — **Single-term q-ary entropy UPPER bound.**  For `2 ≤ q`, `0 < k`, `k < n`: `C(n,k) · (q-1)^k ≤ q^{n·
- `theorem CodingTheory.choose_pow_le_qEntropy` [ArkLib/Data/CodingTheory/EntropyVolumeUpperBound.lean:53](../../../ArkLib/Data/CodingTheory/EntropyVolumeUpperBound.lean#L53) — **Per-term `q`-ary entropy upper bound.** For `2 ≤ q`, `0 < k`, `k < n`, `C(n,k) · (q-1)^k ≤ q^{n ·

### `coeff_ehQ_eq_leading` (2 declarations, 2 files)

- `lemma MvPolynomial.coeff_ehQ_eq_leading` [ArkLib/ToMathlib/RestrictedSumset.lean:223](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L223) — The coefficient of the top monomial `X₀^{n-1} X₁^{n-2}` in `ehQ C'` (with `\|C'\| = 2(n-2)`) equals it
- `lemma MvPolynomial.coeff_ehQ_eq_leading` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:278](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L278) — `ehQ h Cset` differs from the leading part `vdmX h · y^{\|Cset\|}` by a polynomial of strictly smaller

### `coeff_zero_of_natDegree_lt` (2 declarations, 2 files)

- `lemma ProximityGap.coeff_zero_of_natDegree_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:694](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L694) — (no docstring)
- `lemma ProximityGap.coeff_zero_of_natDegree_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:31](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L31) — (no docstring)

### `collisionStep` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.collisionStep` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L52) — **The anchored per-step collision event**: the query was fresh (a genuine sample), and the sampled a
- `def DuplexSpongeFS.EagerLazyDS.collisionStep` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L52) — **The anchored per-step collision event**: the query was fresh (a genuine sample), and the sampled a

### `consistentFrom_eraseIdx_classRed` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_eraseIdx_classRed` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:527](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L527) — A class-redundant erasure preserves consistency in a consistent log.
- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_eraseIdx_classRed` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:527](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L527) — A class-redundant erasure preserves consistency in a consistent log.

### `consistentFrom_eraseIdx_of_noop` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_eraseIdx_of_noop` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:352](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L352) — Erasing a no-op entry preserves consistency.
- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_eraseIdx_of_noop` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:352](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L352) — Erasing a no-op entry preserves consistency.

### `consistentFrom_prefix_getElem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_prefix_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:44](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L44) — Consistency localizes: on a consistent log, entry `k` is consistent with the cache folded over the s
- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_prefix_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:44](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L44) — Consistency localizes: on a consistent log, entry `k` is consistent with the cache folded over the s

### `consistentFrom_removeRedundantEntryDSPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:548](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L548) — Consistency survives the full paper dedup pass.
- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:548](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L548) — Consistency survives the full paper dedup pass.

### `consistentFrom_split` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:820](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L820) — `ConsistentFrom` gives entry-consistency at every split point against the fold cache of the prefix.
- `theorem DuplexSpongeFS.EagerLazyDS.consistentFrom_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:820](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L820) — `ConsistentFrom` gives entry-consistency at every split point against the fold cache of the prefix.

### `consistent_fwd_hit_pair_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistent_fwd_hit_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:757](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L757) — A consistent forward hit puts the entry's exact pair in the cache: if the running cache already hold
- `theorem DuplexSpongeFS.EagerLazyDS.consistent_fwd_hit_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:757](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L757) — A consistent forward hit puts the entry's exact pair in the cache: if the running cache already hold

### `consistent_inv_hit_pair_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.consistent_inv_hit_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:785](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L785) — A consistent inverse hit puts the entry's exact pair in the cache.
- `theorem DuplexSpongeFS.EagerLazyDS.consistent_inv_hit_pair_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:785](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L785) — A consistent inverse hit puts the entry's exact pair in the cache.

### `cutDeficiency` (2 declarations, 2 files)

- `def AGL24.cutDeficiency` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:65](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L65) — The positive part of the missing head-border count for a Frank cut.
- `def AGL24.cutDeficiency` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:61](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L61) — The positive part of the missing head-border count for a Frank cut.

### `cutDeficiency_eq_zero_of_le` (2 declarations, 2 files)

- `theorem AGL24.cutDeficiency_eq_zero_of_le` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:103](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L103) — (no docstring)
- `theorem AGL24.cutDeficiency_eq_zero_of_le` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:87](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L87) — (no docstring)

### `cutDeficiency_pos_iff` (2 declarations, 2 files)

- `theorem AGL24.cutDeficiency_pos_iff` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:97](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L97) — (no docstring)
- `theorem AGL24.cutDeficiency_pos_iff` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:81](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L81) — (no docstring)

### `cutDeficiency_updateHead_lt` (2 declarations, 2 files)

- `theorem AGL24.cutDeficiency_updateHead_lt` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:141](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L141) — (no docstring)
- `theorem AGL24.cutDeficiency_updateHead_lt` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:146](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L146) — (no docstring)

### `decodeLT_ne_of_val_ne` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:87](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L87) — Distinct codewords decode to distinct polynomials: the decoded polynomial interpolates the codeword
- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:181](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L181) — Distinct smooth codewords decode to distinct univariate polynomials (the decoded polynomial interpol

### `derivative_eval_centreFold_isUnit` (2 declarations, 2 files)

- `theorem ArkLib.XiCertReduction.derivative_eval_centreFold_isUnit` [ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean:110](../../../ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean#L110) — **Separability makes the derivative reading along the surface a UNIT**: `IsCoprime Q (∂_Y Q)` evalua
- `theorem ArkLib.XiCertReduction.derivative_eval_centreFold_isUnit` [ArkLib/ToMathlib/XiCertReduction.lean:141](../../../ArkLib/ToMathlib/XiCertReduction.lean#L141) — **Separability makes the derivative reading along the surface a UNIT**: `IsCoprime Q (∂_Y Q)` evalua

### `div_card_pow_C_le_stepBound` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.div_card_pow_C_le_stepBound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:264](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L264) — The hash-arm arithmetic: `A / \|U\|^C ≤ stepBound` for `A ≤ 2m`.
- `lemma DuplexSpongeFS.EagerLazyDS.div_card_pow_C_le_stepBound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:264](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L264) — The hash-arm arithmetic: `A / \|U\|^C ≤ stepBound` for `A ≤ 2m`.

### `div_le_stepBound_of_le` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.div_le_stepBound_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L287) — The permutation-arm arithmetic: `A / len ≤ stepBound` for `A` below the numerator and `len` above th
- `lemma DuplexSpongeFS.EagerLazyDS.div_le_stepBound_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L287) — The permutation-arm arithmetic: `A / len ≤ stepBound` for `A` below the numerator and `len` above th

### `dsCacheSize_empty` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.dsCacheSize_empty` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:457](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L457) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.dsCacheSize_empty` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:457](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L457) — (no docstring)

### `dsfs_hLHS` (2 declarations, 2 files)

- `theorem Reduction.dsfs_hLHS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:197](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L197) — The annotated (assoc-routed) lift equals the direct lift, for every computation: the DS-hLHS. Induct
- `theorem Reduction.dsfs_hLHS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:202](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L202) — The annotated (assoc-routed) lift equals the direct lift, for every computation: the DS-hLHS. Induct

### `dsfs_hLHS₂` (2 declarations, 2 files)

- `theorem Reduction.dsfs_hLHS₂` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:256](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L256) — Annotated lift through `OptionT (OracleComp base)` (the third path) = direct lift.
- `theorem Reduction.dsfs_hLHS₂` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:261](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L261) — Annotated lift through `OptionT (OracleComp base)` (the third path) = direct lift.

### `dsfs_lift_query_bridge_inl` (2 declarations, 2 files)

- `theorem Reduction.dsfs_lift_query_bridge_inl` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:166](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L166) — Bridge: annotated vs direct lift of a single left-side query.
- `theorem Reduction.dsfs_lift_query_bridge_inl` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:171](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L171) — Bridge: annotated vs direct lift of a single left-side query.

### `dsfs_lift_query_bridge_inl₂` (2 declarations, 2 files)

- `theorem Reduction.dsfs_lift_query_bridge_inl₂` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:226](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L226) — Bridge: annotated vs direct lift of a single left-side query.
- `theorem Reduction.dsfs_lift_query_bridge_inl₂` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:232](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L232) — Bridge: annotated vs direct lift of a single left-side query.

### `dsfs_lift_query_bridge_inr` (2 declarations, 2 files)

- `theorem Reduction.dsfs_lift_query_bridge_inr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:65](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L65) — Bridge: annotated (assoc-routed) vs direct lift of a single right-side query.
- `theorem Reduction.dsfs_lift_query_bridge_inr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:70](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L70) — Bridge: annotated (assoc-routed) vs direct lift of a single right-side query.

### `ePaperReduction_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.ePaperReduction_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1609](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1609) — **`EPaperReduction` is a theorem.** A consistent log exhibiting the paper bad event `EPaper` is anch
- `theorem DuplexSpongeFS.EagerLazyDS.ePaperReduction_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1609](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1609) — **`EPaperReduction` is a theorem.** A consistent log exhibiting the paper bad event `EPaper` is anch

### `ePaper_of_answerCap_pair'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.ePaper_of_answerCap_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean#L52) — C1, unordered form: two first-of-mirror-class slots with distinct entries and equal answer-side capa
- `theorem DuplexSpongeFS.Paper.ePaper_of_answerCap_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean#L52) — C1, unordered form: two first-of-mirror-class slots with distinct entries and equal answer-side capa

### `ePaper_of_fwd_inv_pair'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.ePaper_of_fwd_inv_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean:119](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean#L119) — C1 finisher, forward-form previous step vs inverse-form current step (the CO25 5.12 case `ι > 0`): c
- `theorem DuplexSpongeFS.Paper.ePaper_of_fwd_inv_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean:119](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean#L119) — C1 finisher, forward-form previous step vs inverse-form current step (the CO25 5.12 case `ι > 0`): c

### `ePaper_of_hash_inv_pair'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.ePaper_of_hash_inv_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean:104](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean#L104) — C1 finisher, hash anchor vs inverse-form chain slot (the CO25 5.12 case `ι = 0`): equal answer capac
- `theorem DuplexSpongeFS.Paper.ePaper_of_hash_inv_pair'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean:104](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean#L104) — C1 finisher, hash anchor vs inverse-form chain slot (the CO25 5.12 case `ι = 0`): equal answer capac

### `ePaper_of_jbt_inv_slot'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.ePaper_of_jbt_inv_slot'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:178](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L178) — **5.12 core**: a chain step whose `J_BT` slot carries the *inverse-form* entry fires `EPaper`. Downw
- `theorem DuplexSpongeFS.Paper.ePaper_of_jbt_inv_slot'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:178](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L178) — **5.12 core**: a chain step whose `J_BT` slot carries the *inverse-form* entry fires `EPaper`. Downw

### `e_fork_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.ForkCounter.e_fork_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:159](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L159) — The fork event fires: the family has two elements.
- `theorem DuplexSpongeFS.Sponge316.ForkCounter.e_fork_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:159](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L159) — The fork event fires: the family has two elements.

### `e_func_of_twoSurvivors_fwd_same_input` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.e_func_of_twoSurvivors_fwd_same_input` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:225](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L225) — **`Eprp`/`E_func` landing**: two guarded forward slots with the same input force the permutation-inc
- `lemma DuplexSpongeFS.Sponge316.e_func_of_twoSurvivors_fwd_same_input` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:225](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L225) — **`Eprp`/`E_func` landing**: two guarded forward slots with the same input force the permutation-inc

### `e_h_of_hasFirstHashPermCapNatPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_h_of_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:908](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L908) — **The hash-anchored keystone (paper semantics)**: a raw first-occurrence hash collision forces the p
- `theorem DuplexSpongeFS.Sponge316.e_h_of_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:908](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L908) — **The hash-anchored keystone (paper semantics)**: a raw first-occurrence hash collision forces the p

### `e_h_of_twoSurvivors_hash_hash` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.e_h_of_twoSurvivors_hash_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:256](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L256) — **`Efork,h` landing**: two guarded hash slots sharing the answer capacity force `capacitySegmentDupH
- `lemma DuplexSpongeFS.Sponge316.e_h_of_twoSurvivors_hash_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:256](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L256) — **`Efork,h` landing**: two guarded hash slots sharing the answer capacity force `capacitySegmentDupH

### `e_of_hasFirstCapBeforeInverseAnswerPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:277](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L277) — The inverse-anchored keystone, composed into the combined paper bad event `E`.
- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:277](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L277) — The inverse-anchored keystone, composed into the combined paper bad event `E`.

### `e_of_hasFirstHashPermCapNatPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:935](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L935) — The hash-anchored keystone composed into the combined paper bad event `E`.
- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:935](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L935) — The hash-anchored keystone composed into the combined paper bad event `E`.

### `e_of_hasFirstPermCapacityBeforeForwardOutputPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:639](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L639) — The reshaped keystone, composed into the combined paper bad event `E`.
- `theorem DuplexSpongeFS.Sponge316.e_of_hasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:639](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L639) — The reshaped keystone, composed into the combined paper bad event `E`.

### `e_p_of_hasFirstPermCapacityBeforeForwardOutputPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_p_of_hasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:618](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L618) — **The reshaped keystone (paper semantics)**: a raw first-occurrence permutation-capacity collision f
- `theorem DuplexSpongeFS.Sponge316.e_p_of_hasFirstPermCapacityBeforeForwardOutputPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:618](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L618) — **The reshaped keystone (paper semantics)**: a raw first-occurrence permutation-capacity collision f

### `e_p_of_twoSurvivors_hash_fwd` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.e_p_of_twoSurvivors_hash_fwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:240](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L240) — **`Efork,h,p` landing (permutation-late order)**: a guarded hash slot before a guarded forward slot
- `lemma DuplexSpongeFS.Sponge316.e_p_of_twoSurvivors_hash_fwd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:240](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L240) — **`Efork,h,p` landing (permutation-late order)**: a guarded hash slot before a guarded forward slot

### `e_pinv_of_hasFirstCapBeforeInverseAnswerPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_pinv_of_hasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:261](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L261) — **The inverse-anchored keystone (paper semantics)**: a raw first-occurrence inverse entry whose answ
- `theorem DuplexSpongeFS.Sponge316.e_pinv_of_hasFirstCapBeforeInverseAnswerPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:261](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L261) — **The inverse-anchored keystone (paper semantics)**: a raw first-occurrence inverse entry whose answ

### `e_time_h_honest_dedup_hasForwardCapacityBeforeHash_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_dedup_hasForwardCapacityBeforeHash_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1766](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1766) — Off `E`, the raw first-hash timing witness transports through DSFS dedup to a base-trace `HasForward
- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_dedup_hasForwardCapacityBeforeHash_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1766](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1766) — Off `E`, the raw first-hash timing witness transports through DSFS dedup to a base-trace `HasForward

### `e_time_h_honest_raw_forward_capacity_witness_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_forward_capacity_witness_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1664](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1664) — Off `E`, an honest hash-ordering witness gives the raw collision shape before dedup: the earlier for
- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_forward_capacity_witness_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1664](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1664) — Off `E`, an honest hash-ordering witness gives the raw collision shape before dedup: the earlier for

### `e_time_h_honest_raw_forward_witness_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_forward_witness_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1631](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1631) — Off `E`, an honest hash-ordering witness gives concrete raw trace entries: the anchoring hash query
- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_forward_witness_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1631](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1631) — Off `E`, an honest hash-ordering witness gives concrete raw trace entries: the anchoring hash query

### `e_time_h_honest_raw_hasFirstHashForwardCapacityBeforeHash_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_hasFirstHashForwardCapacityBeforeHash_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1729](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1729) — Strong predicate form of the raw timing witness: off `E`, `E_time_h_honest` produces a forward-befor
- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_hasFirstHashForwardCapacityBeforeHash_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1729](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1729) — Strong predicate form of the raw timing witness: off `E`, `E_time_h_honest` produces a forward-befor

### `e_time_h_honest_raw_hasFirstHashPermCapNatPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:953](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L953) — Off the **paper** combined bad event, an honest hash-timing witness yields the direction-agnostic fi
- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_hasFirstHashPermCapNatPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:953](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L953) — Off the **paper** combined bad event, an honest hash-timing witness yields the direction-agnostic fi

### `e_time_h_honest_raw_hasForwardCapacityBeforeHash_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_hasForwardCapacityBeforeHash_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1698](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1698) — Predicate form of the raw timing witness: off `E`, `E_time_h_honest` produces a concrete forward-bef
- `theorem DuplexSpongeFS.Sponge316.e_time_h_honest_raw_hasForwardCapacityBeforeHash_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1698](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1698) — Predicate form of the raw timing witness: off `E`, `E_time_h_honest` produces a concrete forward-bef

### `e_time_p_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.TimePCounter.e_time_p_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:170](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L170) — The out-of-order-permutation event fires on the countermodel.
- `theorem DuplexSpongeFS.Sponge316.TimePCounter.e_time_p_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:170](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L170) — The out-of-order-permutation event fires on the countermodel.

### `e_time_p_honest_raw_adjacent_forward_witness_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_p_honest_raw_adjacent_forward_witness_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1312](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1312) — Off `E`, an honest permutation-ordering witness gives adjacent raw forward permutation entries: the
- `theorem DuplexSpongeFS.Sponge316.e_time_p_honest_raw_adjacent_forward_witness_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1312](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1312) — Off `E`, an honest permutation-ordering witness gives adjacent raw forward permutation entries: the

### `e_time_p_honest_raw_forward_capacity_witness_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_p_honest_raw_forward_capacity_witness_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1360](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1360) — Off `E`, an honest permutation-ordering witness gives the raw adjacent-forward capacity shape before
- `theorem DuplexSpongeFS.Sponge316.e_time_p_honest_raw_forward_capacity_witness_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1360](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1360) — Off `E`, an honest permutation-ordering witness gives the raw adjacent-forward capacity shape before

### `e_time_p_honest_raw_hasFirstForwardCapacityBeforeForwardOutput_or_prior_reverse_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_p_honest_raw_hasFirstForwardCapacityBeforeForwardOutput_or_prior_reverse_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1534](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1534) — Off `E`, an honest permutation-ordering witness either gives the strengthened raw first-forward pred
- `theorem DuplexSpongeFS.Sponge316.e_time_p_honest_raw_hasFirstForwardCapacityBeforeForwardOutput_or_prior_reverse_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1534](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1534) — Off `E`, an honest permutation-ordering witness either gives the strengthened raw first-forward pred

### `e_time_p_honest_raw_hasForwardCapacityBeforeForwardOutput_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_p_honest_raw_hasForwardCapacityBeforeForwardOutput_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1433](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1433) — Broad predicate form of the raw permutation-timing witness, aligned with the preservation-friendly b
- `theorem DuplexSpongeFS.Sponge316.e_time_p_honest_raw_hasForwardCapacityBeforeForwardOutput_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1433](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1433) — Broad predicate form of the raw permutation-timing witness, aligned with the preservation-friendly b

### `e_time_p_honest_raw_hasInputCapacityBeforeForwardOutput_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.e_time_p_honest_raw_hasInputCapacityBeforeForwardOutput_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1398](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1398) — Predicate form of the raw permutation-timing witness: off `E`, `E_time_p_honest` produces a concrete
- `theorem DuplexSpongeFS.Sponge316.e_time_p_honest_raw_hasInputCapacityBeforeForwardOutput_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1398](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1398) — Predicate form of the raw permutation-timing witness: off `E`, `E_time_p_honest` produces a concrete

### `ehQ` (2 declarations, 2 files)

- `def MvPolynomial.ehQ` [ArkLib/ToMathlib/RestrictedSumset.lean:218](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L218) — **The Erdős–Heilbronn polynomial** for a padded sumset `C'`.
- `def MvPolynomial.ehQ` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:273](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L273) — **The general Erdős–Heilbronn polynomial** for a padded sumset `C'`.

### `ehY` (2 declarations, 2 files)

- `def MvPolynomial.ehY` [ArkLib/ToMathlib/RestrictedSumset.lean:169](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L169) — Abbreviation for the "diagonal" variable `y = X₀ + X₁`.
- `def MvPolynomial.ehY` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:191](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L191) — The "diagonal" variable `y = ∑_k X k`.

### `entryConsistent` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.entryConsistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L67) — A log entry agrees with a cache: if its query is cached, the logged answer is the cached one.
- `def DuplexSpongeFS.EagerLazyDS.entryConsistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L67) — A log entry agrees with a cache: if its query is cached, the logged answer is the cached one.

### `entryFwdKey` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.entryFwdKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:348](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L348) — The forward key inserted by an entry (`none` for a hash entry).
- `def DuplexSpongeFS.EagerLazyDS.entryFwdKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:348](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L348) — The forward key inserted by an entry (`none` for a hash entry).

### `entryInvKey` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.entryInvKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:357](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L357) — The inverse key inserted by an entry (`none` for a hash entry). For a forward entry `⟨inr (inl a), b
- `def DuplexSpongeFS.EagerLazyDS.entryInvKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:357](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L357) — The inverse key inserted by an entry (`none` for a hash entry). For a forward entry `⟨inr (inl a), b

### `epsMCAP_interleaved_eq` (2 declarations, 2 files)

- `theorem ProximityGapP.epsMCAP_interleaved_eq` [ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCAP.lean:235](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCAP.lean#L235) — **Jo26 exact interleaving invariance for `epsMCAP`.**  The general power-generator MCA error is unch
- `theorem ProximityGapP.epsMCAP_interleaved_eq` [ArkLib/Data/CodingTheory/ProximityGap/Jo26PowerGeneratorInterleaving.lean:288](../../../ArkLib/Data/CodingTheory/ProximityGap/Jo26PowerGeneratorInterleaving.lean#L288) — **[Jo26] Corollary 4.5 (power-generator case): the general-`parℓ` MCA error is exactly invariant und

### `epsMCAP_interleaved_le_epsMCAP` (2 declarations, 2 files)

- `theorem ProximityGapP.epsMCAP_interleaved_le_epsMCAP` [ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCAP.lean:169](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCAP.lean#L169) — The Jo26 small-seed direction for `epsMCAP`: because the bad-seed subspaces are indexed by the seed
- `theorem ProximityGapP.epsMCAP_interleaved_le_epsMCAP` [ArkLib/Data/CodingTheory/ProximityGap/Jo26PowerGeneratorInterleaving.lean:215](../../../ArkLib/Data/CodingTheory/ProximityGap/Jo26PowerGeneratorInterleaving.lean#L215) — **`ε_mcaP(C^≡t, exp, δ) ≤ ε_mcaP(C, exp, δ)`** ([Jo26] Theorem 4.4, power-generator case).  The bad-

### `epsMCAP_le_epsMCAP_interleaved` (2 declarations, 2 files)

- `theorem ProximityGapP.epsMCAP_le_epsMCAP_interleaved` [ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCAP.lean:122](../../../ArkLib/Data/CodingTheory/ProximityGap/InterleavingStabilityMCAP.lean#L122) — Zero-row embedding: a base `epsMCAP` bad stack embeds into the interleaved code by placing the whole
- `theorem ProximityGapP.epsMCAP_le_epsMCAP_interleaved` [ArkLib/Data/CodingTheory/ProximityGap/Jo26PowerGeneratorInterleaving.lean:159](../../../ArkLib/Data/CodingTheory/ProximityGap/Jo26PowerGeneratorInterleaving.lean#L159) — **`ε_mcaP(C, exp, δ) ≤ ε_mcaP(C^≡t, exp, δ)`** ([Jo26] Theorem 4.2, lower half, power-generator case

### `evalEval_congr` (2 declarations, 2 files)

- `lemma R15.evalEval_congr` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:302](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L302) — The double evaluation `Q(a, f(a))` depends on `f` only through the value `f(a)`.
- `lemma R15.evalEval_congr` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:302](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L302) — The double evaluation `Q(a, f(a))` depends on `f` only through the value `f(a)`.

### `evalEval_radical_eq_zero` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.evalEval_radical_eq_zero` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:292](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L292) — The centre fold of the surface roots the RADICAL of the fiber at every curve parameter — mirror of `
- `theorem ArkLib.RadicalWire304.evalEval_radical_eq_zero` [ArkLib/ToMathlib/RadicalAssembler.lean:311](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L311) — The centre fold of the surface roots the RADICAL of the fiber at every curve parameter — mirror of `

### `evalX_eval_centreFold_eq_zero` (2 declarations, 2 files)

- `theorem ArkLib.XiCertReduction.evalX_eval_centreFold_eq_zero` [ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean:86](../../../ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean#L86) — **The centre fold is a global root of the specialized trivariate**: `(evalX (C x₀) R).eval (w.eval (
- `theorem ArkLib.XiCertReduction.evalX_eval_centreFold_eq_zero` [ArkLib/ToMathlib/XiCertReduction.lean:117](../../../ArkLib/ToMathlib/XiCertReduction.lean#L117) — **The centre fold is a global root of the specialized trivariate**: `(evalX (C x₀) R).eval (w.eval (

### `eval_ehQ_eq_zero` (2 declarations, 2 files)

- `lemma MvPolynomial.eval_ehQ_eq_zero` [ArkLib/ToMathlib/RestrictedSumset.lean:294](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L294) — `ehQ Cset` vanishes at every point `s : Fin 2 → F` whose two coordinates either coincide, or sum to
- `lemma MvPolynomial.eval_ehQ_eq_zero` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:335](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L335) — `ehQ h Cset` vanishes at every point `s : Fin h → F` whose coordinates are not all distinct, or whos

### `eval_eval_eq_sum` (2 declarations, 2 files)

- `lemma R15.eval_eval_eq_sum` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:293](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L293) — Expansion of the double evaluation `Q(a, f(a))` as a sum over the `Y`-support.
- `lemma R15.eval_eval_eq_sum` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:293](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L293) — Expansion of the double evaluation `Q(a, f(a))` as a sum over the `Y`-support.

### `eval_natDegree_le_of_coeff_le` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.eval_natDegree_le_of_coeff_le` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:98](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L98) — The bivariate eval-degree bound (the fiber-level mirror of `SectionGlobalLift.eval_section_natDegree
- `theorem ArkLib.RadicalWire304.eval_natDegree_le_of_coeff_le` [ArkLib/ToMathlib/RadicalAssembler.lean:117](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L117) — The bivariate eval-degree bound (the fiber-level mirror of `SectionGlobalLift.eval_section_natDegree

### `exists_border_head_outside_of_deficient_cut` (2 declarations, 2 files)

- `theorem AGL24.exists_border_head_outside_of_deficient_cut` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:401](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L401) — A strictly deficient proper WPC cut has a crossing edge whose head lies outside the cut. This is the
- `theorem AGL24.exists_border_head_outside_of_deficient_cut` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:177](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L177) — A strictly deficient proper WPC cut has a crossing edge whose head lies outside the cut. This is the

### `exists_border_head_outside_of_positive_deficiency` (2 declarations, 2 files)

- `theorem AGL24.exists_border_head_outside_of_positive_deficiency` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:418](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L418) — Positive `cutDeficiency` form of `exists_border_head_outside_of_deficient_cut`.
- `theorem AGL24.exists_border_head_outside_of_positive_deficiency` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:197](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L197) — Positive `cutDeficiency` form of `exists_border_head_outside_of_deficient_cut`.

### `exists_border_not_head_of_headBorder_lt_border` (2 declarations, 2 files)

- `theorem AGL24.exists_border_not_head_of_headBorder_lt_border` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:386](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L386) — If the head-border count is strictly smaller than the full border count, some border edge has not ye
- `theorem AGL24.exists_border_not_head_of_headBorder_lt_border` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:161](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L161) — If the head-border count is strictly smaller than the full border count, some border edge has not ye

### `exists_far_codeword_of_curveDecodable` (2 declarations, 2 files)

- `theorem ProximityGap.exists_far_codeword_of_curveDecodable` [ArkLib/Data/CodingTheory/ProximityGap/GG25NonCovering.lean:109](../../../ArkLib/Data/CodingTheory/ProximityGap/GG25NonCovering.lean#L109) — **[Jo26] Lemma 5.4 (curve decodability gives a non-covering condition).** A nonzero `(ℓ, δ, a, b)`-c
- `theorem ProximityGap.exists_far_codeword_of_curveDecodable` [ArkLib/Data/CodingTheory/ProximityGap/Jo26CurveNonCovering.lean:53](../../../ArkLib/Data/CodingTheory/ProximityGap/Jo26CurveNonCovering.lean#L53) — **[Jo26] Lemma 5.4 (curve decodability gives a non-covering condition).**  A nonzero `F`-submodule c

### `exists_updateHead_decreases_cutDeficiency_of_border_head_outside` (2 declarations, 2 files)

- `theorem AGL24.exists_updateHead_decreases_cutDeficiency_of_border_head_outside` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:428](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L428) — (no docstring)
- `theorem AGL24.exists_updateHead_decreases_cutDeficiency_of_border_head_outside` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:207](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L207) — (no docstring)

### `exists_updateHead_decreases_positive_deficiency_cut` (2 declarations, 2 files)

- `theorem AGL24.exists_updateHead_decreases_positive_deficiency_cut` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:445](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L445) — Positive-deficiency local reorientation step for a single cut. This is only the F3 one-cut decrease
- `theorem AGL24.exists_updateHead_decreases_positive_deficiency_cut` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:224](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L224) — Positive-deficiency local reorientation step for a single cut. This is only the one-cut decrease bri

### `famC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TimePCounter.famC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:104](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L104) — The singleton backtrack family `{seqC}` (maximality is vacuous).
- `def DuplexSpongeFS.Sponge316.TimePCounter.famC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:104](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L104) — The singleton backtrack family `{seqC}` (maximality is vacuous).

### `famF` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.famF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:135](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L135) — The two-element backtrack family `{seqOne, seqTwo}`; maximality holds because neither chain's state
- `def DuplexSpongeFS.Sponge316.ForkCounter.famF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:135](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L135) — The two-element backtrack family `{seqOne, seqTwo}`; maximality holds because neither chain's state

### `fiber_ne_zero` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.fiber_ne_zero` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:71](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L71) — Nonzeroness of the fiber — the ONLY consequence of `separable_evalX` used in the radical split/branc
- `theorem ArkLib.RadicalWire304.fiber_ne_zero` [ArkLib/ToMathlib/RadicalAssembler.lean:90](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L90) — Nonzeroness of the fiber — the ONLY consequence of `separable_evalX` used in the radical split/branc

### `finalCheckTight_perfectCompleteness` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.finalCheckTight_perfectCompleteness` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:299](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L299) — **The tight terminal completeness leaf `h₈`**: perfect completeness of the tight chain's zero-round
- `theorem Spartan.Spec.Bricks.finalCheckTight_perfectCompleteness` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:247](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L247) — **Completeness leaf for the tight terminal check** (#329, B7): `finalCheckTight` carries the conjoin

### `find` (4 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1097](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1097) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1105](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1105) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1097](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1097) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1105](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1105) — (no docstring)

### `finset_card_ge_of_pred_natCast_le_ennreal_lt` (2 declarations, 2 files)

- `lemma ProximityGap.finset_card_ge_of_pred_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:127](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L127) — (no docstring)
- `theorem ProximityGap.finset_card_ge_of_pred_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:131](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L131) — Convert an ENNReal lower bound on a finite set cardinality into a natural number weak cardinality bo

### `finset_card_gt_of_natCast_le_ennreal_lt` (2 declarations, 2 files)

- `lemma ProximityGap.finset_card_gt_of_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:120](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L120) — (no docstring)
- `theorem ProximityGap.finset_card_gt_of_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:120](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L120) — Convert an ENNReal lower bound on a finite set cardinality into a natural number strict cardinality

### `firstForwardNat_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstForwardNat_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:659](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L659) — **One-step preservation**: erasing one redundant entry preserves the strengthened forward-before-fir
- `lemma DuplexSpongeFS.Sponge316.firstForwardNat_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:659](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L659) — **One-step preservation**: erasing one redundant entry preserves the strengthened forward-before-fir

### `firstForwardNat_of_first` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstForwardNat_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:612](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L612) — Convert the public finite-index first-forward witness into the private natural-index form.
- `lemma DuplexSpongeFS.Sponge316.firstForwardNat_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:612](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L612) — Convert the public finite-index first-forward witness into the private natural-index form.

### `firstForwardNat_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstForwardNat_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:789](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L789) — **Fixpoint preservation**: dedup preserves the first-forward output-capacity collision shape as the
- `lemma DuplexSpongeFS.Sponge316.firstForwardNat_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:789](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L789) — **Fixpoint preservation**: dedup preserves the first-forward output-capacity collision shape as the

### `firstGuardD_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L118) — Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- `lemma DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L118) — Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.

### `firstGuard_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L69) — Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- `lemma DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L69) — Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.

### `firstHashPermNatPaper_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstHashPermNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:741](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L741) — **One-step preservation (paper)**: erasing one paper-redundant entry preserves the first-hash collis
- `lemma DuplexSpongeFS.Sponge316.firstHashPermNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:741](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L741) — **One-step preservation (paper)**: erasing one paper-redundant entry preserves the first-hash collis

### `firstHashPermNatPaper_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstHashPermNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:879](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L879) — **Fixpoint preservation (paper)**: dedup carries the first-hash collision shape to the broad base-tr
- `lemma DuplexSpongeFS.Sponge316.firstHashPermNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:879](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L879) — **Fixpoint preservation (paper)**: dedup carries the first-hash collision shape to the broad base-tr

### `firstInvNatPaper_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstInvNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:149](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L149) — **One-step preservation (paper semantics)**: erasing one paper-redundant entry preserves the first-o
- `lemma DuplexSpongeFS.Sponge316.firstInvNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:149](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L149) — **One-step preservation (paper semantics)**: erasing one paper-redundant entry preserves the first-o

### `firstInvNatPaper_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstInvNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L234) — **Fixpoint preservation (paper semantics)**: dedup preserves the inverse-anchored shape.
- `lemma DuplexSpongeFS.Sponge316.firstInvNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L234) — **Fixpoint preservation (paper semantics)**: dedup preserves the inverse-anchored shape.

### `firstNat_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstNat_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:411](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L411) — **One-step preservation**: erasing one redundant entry preserves the strengthened forward-before-fir
- `lemma DuplexSpongeFS.Sponge316.firstNat_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:411](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L411) — **One-step preservation**: erasing one redundant entry preserves the strengthened forward-before-fir

### `firstNat_of_first` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstNat_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:360](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L360) — Convert the public finite-index first-hash witness into the private natural-index form.
- `lemma DuplexSpongeFS.Sponge316.firstNat_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:360](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L360) — Convert the public finite-index first-hash witness into the private natural-index form.

### `firstNat_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstNat_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:502](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L502) — **Fixpoint preservation**: dedup preserves the first-hash forward-capacity collision shape as the ba
- `lemma DuplexSpongeFS.Sponge316.firstNat_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:502](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L502) — **Fixpoint preservation**: dedup preserves the first-hash forward-capacity collision shape as the ba

### `firstOfClassAt_of_noRedundant` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.firstOfClassAt_of_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L53) — **Certificate freshness**: the dedup's `NoRedundantEntryDSPaper` certificate gives first-of-class at
- `theorem DuplexSpongeFS.EagerLazyDS.firstOfClassAt_of_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L53) — **Certificate freshness**: the dedup's `NoRedundantEntryDSPaper` certificate gives first-of-class at

### `firstOfClassAt_of_perm_index'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.firstOfClassAt_of_perm_index'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean#L67) — **Index bridge**: a nonterminal `BacktrackSequence.Index` permutation slot is a first-of-mirror-clas
- `theorem DuplexSpongeFS.Paper.firstOfClassAt_of_perm_index'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean:67](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean#L67) — **Index bridge**: a nonterminal `BacktrackSequence.Index` permutation slot is a first-of-mirror-clas

### `firstPermNatPaper_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:404](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L404) — **One-step preservation (paper semantics)**: erasing one paper-redundant entry preserves the first-p
- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:404](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L404) — **One-step preservation (paper semantics)**: erasing one paper-redundant entry preserves the first-p

### `firstPermNatPaper_of_first` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:346](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L346) — Convert the public finite-index paper witness into the natural-index form.
- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:346](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L346) — Convert the public finite-index paper witness into the natural-index form.

### `firstPermNatPaper_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:582](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L582) — **Fixpoint preservation (paper semantics)**: dedup preserves the first-perm collision shape as the b
- `lemma DuplexSpongeFS.Sponge316.firstPermNatPaper_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:582](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L582) — **Fixpoint preservation (paper semantics)**: dedup preserves the first-perm collision shape as the b

### `firstSumcheck_rbrKnowledgeSoundness_honest` (2 declarations, 2 files)

- `theorem Spartan.Spec.firstSumcheck_rbrKnowledgeSoundness_honest` [ArkLib/ProofSystem/Spartan/FirstSumcheckComplete.lean:202](../../../ArkLib/ProofSystem/Spartan/FirstSumcheckComplete.lean#L202) — **First sum-check phase round-by-round knowledge soundness (issue #114).** The Spartan lift of the g
- `theorem Spartan.Spec.firstSumcheck_rbrKnowledgeSoundness_honest` [ArkLib/ProofSystem/Spartan/SumcheckKnowledgeLeaves.lean:82](../../../ArkLib/ProofSystem/Spartan/SumcheckKnowledgeLeaves.lean#L82) — The first Spartan sum-check RBR-KS leaf over the honest transported relation contract, reduced to th

### `foldl_hash_provenance` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_hash_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1205](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1205) — **Hash-cache provenance (whole fold).**
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_hash_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1205](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1205) — **Hash-cache provenance (whole fold).**

### `foldl_pair_provenance` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_pair_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:740](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L740) — **Pair provenance (whole fold)**: a pair in the final cache was in the start cache or inserted by so
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_pair_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:740](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L740) — **Pair provenance (whole fold)**: a pair in the final cache was in the start cache or inserted by so

### `foldl_stepCache_fwdNodup` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_fwdNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:702](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L702) — Forward-key distinctness is preserved along a whole non-anchored fold.
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_fwdNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:702](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L702) — Forward-key distinctness is preserved along a whole non-anchored fold.

### `foldl_stepCache_hash_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_hash_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1369](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1369) — The hash cache only grows along the whole fold.
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_hash_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1369](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1369) — The hash cache only grows along the whole fold.

### `foldl_stepCache_pair_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_pair_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:102](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L102) — Permutation pairs persist through any fold suffix.
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_pair_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:102](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L102) — Permutation pairs persist through any fold suffix.

### `foldl_stepCache_perm_sublist` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_perm_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:329](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L329) — The permutation cache only grows along the whole fold.
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_stepCache_perm_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:329](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L329) — The permutation cache only grows along the whole fold.

### `foldl_stepCache_take_from_getElem` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.foldl_stepCache_take_from_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:408](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L408) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.foldl_stepCache_take_from_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:408](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L408) — (no docstring)

### `foldl_take_succ_eq` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.foldl_take_succ_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L90) — Folding one more prefix entry is one `stepCache` step.
- `theorem DuplexSpongeFS.EagerLazyDS.foldl_take_succ_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L90) — Folding one more prefix entry is one `stepCache` step.

### `for` (2 declarations, 2 files)

- `theorem for` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessProof.lean:14](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessProof.lean#L14) — (no docstring)
- `theorem for` [ArkLib/ProofSystem/Logup/Security/Soundness.lean:46](../../../ArkLib/ProofSystem/Logup/Security/Soundness.lean#L46) — (no docstring)

### `forwardEntry` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.forwardEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:343](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L343) — Private shorthand for a concrete forward permutation query-answer entry.
- `def DuplexSpongeFS.Sponge316.forwardEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:343](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L343) — Private shorthand for a concrete forward permutation query-answer entry.

### `forwardEntryC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.forwardEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L58) — (no docstring)
- `def DuplexSpongeFS.Sponge316.forwardEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L58) — (no docstring)

### `forwardEntryD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.forwardEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:54](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L54) — (no docstring)
- `def DuplexSpongeFS.Sponge316.forwardEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:54](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L54) — (no docstring)

### `forwardEntryP` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.forwardEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:245](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L245) — (no docstring)
- `def DuplexSpongeFS.Sponge316.forwardEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:245](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L245) — (no docstring)

### `forward_getElem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.forward_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:956](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L956) — Off `E`, a trace slot known to be either the forward or inverse entry for one sponge step must be th
- `theorem DuplexSpongeFS.Sponge316.forward_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:956](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L956) — Off `E`, a trace slot known to be either the forward or inverse entry for one sponge step must be th

### `fresh_at_firstOfClass_hash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:61](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L61) — **Freshness (hash case)**: at a class-first slot holding a hash entry, the hash cache misses.
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:61](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L61) — **Freshness (hash case)**: at a class-first slot holding a hash entry, the hash cache misses.

### `fresh_at_firstOfClass_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L90) — **Freshness (forward case)**: at a class-first slot holding a forward permutation entry, the pair ca
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L90) — **Freshness (forward case)**: at a class-first slot holding a forward permutation entry, the pair ca

### `fresh_at_firstOfClass_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:132](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L132) — **Freshness (inverse case)**: at a class-first slot holding an inverse permutation entry, the pair c
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:132](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L132) — **Freshness (inverse case)**: at a class-first slot holding an inverse permutation entry, the pair c

### `fresh_fwd_inserts` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_fwd_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1272](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1272) — A fresh forward entry's pair ends up in the final fold cache.
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_fwd_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1272](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1272) — A fresh forward entry's pair ends up in the final fold cache.

### `fresh_hash_inserts` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_hash_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1377](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1377) — A fresh hash entry's answer ends up cached in the final fold.
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_hash_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1377](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1377) — A fresh hash entry's answer ends up cached in the final fold.

### `fresh_inv_inserts` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fresh_inv_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1287) — A fresh inverse entry's pair ends up in the final fold cache.
- `theorem DuplexSpongeFS.EagerLazyDS.fresh_inv_inserts` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1287) — A fresh inverse entry's pair ends up in the final fold cache.

### `fwdInState` (2 declarations, 2 files)

- `def DuplexSpongeFS.Paper.fwdInState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L58) — Query-state extractor for forward-permutation entries (avoids the dependent-`Sigma` `HEq` when compa
- `def DuplexSpongeFS.Paper.fwdInState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L58) — Query-state extractor for forward-permutation entries (avoids the dependent-`Sigma` `HEq` when compa

### `fwdInStateD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.fwdInStateD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:272](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L272) — Query-state extractor for forward-permutation entries.
- `def DuplexSpongeFS.Sponge316.fwdInStateD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:272](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L272) — Query-state extractor for forward-permutation entries.

### `fwdOutState` (2 declarations, 2 files)

- `def DuplexSpongeFS.Paper.fwdOutState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:65](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L65) — Answer-state extractor for forward-permutation entries.
- `def DuplexSpongeFS.Paper.fwdOutState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:65](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L65) — Answer-state extractor for forward-permutation entries.

### `fwdOutStateD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.fwdOutStateD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:279](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L279) — Answer-state extractor for forward-permutation entries.
- `def DuplexSpongeFS.Sponge316.fwdOutStateD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:279](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L279) — Answer-state extractor for forward-permutation entries.

### `fwd_entry_fresh` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fwd_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:861](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L861) — **A non-redundant forward entry is fresh.** If `⟨inr (inl a), b⟩` occurs in a consistent log with no
- `theorem DuplexSpongeFS.EagerLazyDS.fwd_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:861](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L861) — **A non-redundant forward entry is fresh.** If `⟨inr (inl a), b⟩` occurs in a consistent log with no

### `fwd_fresh_cap_new` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fwd_fresh_cap_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:552](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L552) — A fresh forward step that is not an anchored collision yields an answer capacity that is neither an
- `theorem DuplexSpongeFS.EagerLazyDS.fwd_fresh_cap_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:552](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L552) — A fresh forward step that is not an anchored collision yields an answer capacity that is neither an

### `fwd_hit_sameClass_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.fwd_hit_sameClass_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:773](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L773) — **Piece (A2c)**: in a fold from empty over `L`, a consistent forward entry `⟨inr (inl a), b⟩` whose
- `theorem DuplexSpongeFS.EagerLazyDS.fwd_hit_sameClass_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:773](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L773) — **Piece (A2c)**: in a fold from empty over `L`, a consistent forward entry `⟨inr (inl a), b⟩` whose

### `game_apply_eq` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge314.K1.game_apply_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:83](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L83) — For every sampled carrier `c`, the logged eager game on `P` is deterministic: it returns the inverse
- `lemma DuplexSpongeFS.Sponge314.K1.game_apply_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:83](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L83) — For every sampled carrier `c`, the logged eager game on `P` is deterministic: it returns the inverse

### `game_eq` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge314.K1.game_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:92](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L92) — The full game equals sampling a carrier and returning the deterministic logged output.
- `lemma DuplexSpongeFS.Sponge314.K1.game_eq` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:92](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L92) — The full game equals sampling a carrier and returning the deterministic logged output.

### `getElem_idx_congr` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L49) — Transport a `List.getElem` along a `Nat` index equality.
- `lemma DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L49) — Transport a `List.getElem` along a `Nat` index equality.

### `getElem_idx_congrD` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L286) — Transport a `List.getElem` along a `Nat` index equality.
- `lemma DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L286) — Transport a `List.getElem` along a `Nat` index equality.

### `getElem_list_congr` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L53) — Transport a `List.getElem` along a list equality.
- `lemma DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L53) — Transport a `List.getElem` along a list equality.

### `getElem_list_congrD` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L292) — Transport a `List.getElem` along a list equality.
- `lemma DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L292) — Transport a `List.getElem` along a list equality.

### `getElem_mem_take` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.getElem_mem_take` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:896](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L896) — An earlier-indexed element lies in the prefix `take p`.
- `theorem DuplexSpongeFS.EagerLazyDS.getElem_mem_take` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:896](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L896) — An earlier-indexed element lies in the prefix `take p`.

### `get_eraseIdx_after` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.get_eraseIdx_after` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:80](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L80) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.get_eraseIdx_after` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:80](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L80) — (no docstring)

### `get_eraseIdx_before` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.get_eraseIdx_before` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:60](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L60) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.get_eraseIdx_before` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:60](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L60) — (no docstring)

### `hasCapBeforeInverseAnswerPaper_of_first` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasCapBeforeInverseAnswerPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:136](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L136) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.hasCapBeforeInverseAnswerPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:136](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L136) — (no docstring)

### `hasFirstForwardCapacityBeforeForwardOutput_current_not_redundant` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasFirstForwardCapacityBeforeForwardOutput_current_not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:584](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L584) — The strong permutation-ordering predicate carries the nonredundancy proof needed for its later forwa
- `theorem DuplexSpongeFS.Sponge316.hasFirstForwardCapacityBeforeForwardOutput_current_not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:584](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L584) — The strong permutation-ordering predicate carries the nonredundancy proof needed for its later forwa

### `hasFirstHashForwardCapacityBeforeHash_hash_not_redundant` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasFirstHashForwardCapacityBeforeHash_hash_not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1041](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1041) — The strong forward-before-hash predicate carries exactly the nonredundancy proof needed for its hash
- `theorem DuplexSpongeFS.Sponge316.hasFirstHashForwardCapacityBeforeHash_hash_not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1041](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1041) — The strong forward-before-hash predicate carries exactly the nonredundancy proof needed for its hash

### `hasFirstHashFwdCapNat_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:97](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L97) — **One-step preservation**: erasing one redundant entry preserves `HasFirstHashFwdCapNat`.
- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:97](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L97) — **One-step preservation**: erasing one redundant entry preserves `HasFirstHashFwdCapNat`.

### `hasFirstHashFwdCapNat_of_first` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L68) — The `Fin`-indexed first-occurrence shape implies the ℕ-indexed one.
- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L68) — The `Fin`-indexed first-occurrence shape implies the ℕ-indexed one.

### `hasFirstHashFwdCapNat_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:194](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L194) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves `HasFirstHashFwdCa
- `lemma DuplexSpongeFS.Sponge316.hasFirstHashFwdCapNat_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:194](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L194) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves `HasFirstHashFwdCa

### `hasFirstPermCapacityBeforeForwardOutputPaper_current_not_redundant` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasFirstPermCapacityBeforeForwardOutputPaper_current_not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:315](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L315) — The paper first-occurrence collision shape carries the nonredundancy proof for its forward anchor.
- `theorem DuplexSpongeFS.Sponge316.hasFirstPermCapacityBeforeForwardOutputPaper_current_not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:315](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L315) — The paper first-occurrence collision shape carries the nonredundancy proof for its forward anchor.

### `hasForwardCapacityBeforeForwardOutput_of_first` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeForwardOutput_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:555](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L555) — Forgetting the first-occurrence guard leaves the broad forward-before-forward-output shape.
- `theorem DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeForwardOutput_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:555](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L555) — Forgetting the first-occurrence guard leaves the broad forward-before-forward-output shape.

### `hasForwardCapacityBeforeForwardOutput_of_firstForwardNat` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeForwardOutput_of_firstForwardNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:644](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L644) — Convert the private natural-index witness back to the public broad base-trace shape.
- `lemma DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeForwardOutput_of_firstForwardNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:644](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L644) — Convert the private natural-index witness back to the public broad base-trace shape.

### `hasForwardCapacityBeforeForwardOutput_of_input` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeForwardOutput_of_input` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:163](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L163) — The input-side-only permutation-ordering shape is a special case of the broader preservation-friendl
- `theorem DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeForwardOutput_of_input` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:163](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L163) — The input-side-only permutation-ordering shape is a special case of the broader preservation-friendl

### `hasForwardCapacityBeforeForwardOutput_removeRedundant_of_first` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeForwardOutput_removeRedundant_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:817](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L817) — Public dedup bridge for the M2c permutation-timing path: the strengthened raw first-forward witness
- `theorem DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeForwardOutput_removeRedundant_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:817](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L817) — Public dedup bridge for the M2c permutation-timing path: the strengthened raw first-forward witness

### `hasForwardCapacityBeforeHash_of_first` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeHash_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:192](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L192) — Forgetting the first-occurrence guard leaves the ordinary forward-before-hash capacity shape.
- `theorem DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeHash_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:192](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L192) — Forgetting the first-occurrence guard leaves the ordinary forward-before-hash capacity shape.

### `hasForwardCapacityBeforeHash_of_firstNat` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeHash_of_firstNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:384](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L384) — Convert the private natural-index witness back to the public base-trace collision shape.
- `lemma DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeHash_of_firstNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:384](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L384) — Convert the private natural-index witness back to the public base-trace collision shape.

### `hasForwardCapacityBeforeHash_of_nat` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeHash_of_nat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L85) — The ℕ-indexed shape implies the plain (`Fin`-indexed, no firstness) collision shape.
- `lemma DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeHash_of_nat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L85) — The ℕ-indexed shape implies the plain (`Fin`-indexed, no firstness) collision shape.

### `hasForwardCapacityBeforeHash_removeRedundant_of_first` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeHash_removeRedundant_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:529](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L529) — Public dedup bridge for the M2c hash-timing path: the strengthened raw first-hash witness survives `
- `theorem DuplexSpongeFS.Sponge316.hasForwardCapacityBeforeHash_removeRedundant_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:529](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L529) — Public dedup bridge for the M2c hash-timing path: the strengthened raw first-hash witness survives `

### `hasFwdKey` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.hasFwdKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:340](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L340) — Whether a permutation cache already holds the forward key `a`.
- `def DuplexSpongeFS.EagerLazyDS.hasFwdKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:340](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L340) — Whether a permutation cache already holds the forward key `a`.

### `hasFwdKey_foldl_imp` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hasFwdKey_foldl_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:436](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L436) — A forward key present after the whole fold was either present at the start or inserted by some entry
- `theorem DuplexSpongeFS.EagerLazyDS.hasFwdKey_foldl_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:436](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L436) — A forward key present after the whole fold was either present at the start or inserted by some entry

### `hasFwdKey_stepCache_imp` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hasFwdKey_stepCache_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:400](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L400) — One fold step can only create the forward key it inserts: if a key is present after the step but not
- `theorem DuplexSpongeFS.EagerLazyDS.hasFwdKey_stepCache_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:400](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L400) — One fold step can only create the forward key it inserts: if a key is present after the step but not

### `hasHashEntry_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:265](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L265) — **One-step preservation**: erasing a redundant entry preserves a concrete hash entry.
- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:265](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L265) — **One-step preservation**: erasing a redundant entry preserves a concrete hash entry.

### `hasHashEntry_eraseIdxPaper` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_eraseIdxPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:162](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L162) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_eraseIdxPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:162](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L162) — (no docstring)

### `hasHashEntry_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:306](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L306) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:306](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L306) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr

### `hasHashEntry_removeRedundantPaper` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L203) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
- `lemma DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L203) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr

### `hasHashEntry_removeRedundantPaper_of_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:227](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L227) — Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
- `theorem DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:227](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L227) — Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica

### `hasHashEntry_removeRedundant_of_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:330](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L330) — Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
- `theorem DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:330](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L330) — Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica

### `hasHashPermCapBeforeHashPaper_of_nat` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasHashPermCapBeforeHashPaper_of_nat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:728](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L728) — (no docstring)
- `lemma DuplexSpongeFS.Sponge316.hasHashPermCapBeforeHashPaper_of_nat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:728](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L728) — (no docstring)

### `hasInvEntry_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasInvEntry_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:845](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L845) — **One-step preservation**: erasing a redundant entry preserves `HasInvEntry`.
- `lemma DuplexSpongeFS.Sponge316.hasInvEntry_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:845](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L845) — **One-step preservation**: erasing a redundant entry preserves `HasInvEntry`.

### `hasInvEntry_implies_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasInvEntry_implies_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:929](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L929) — **Keystone**: an inverse-permutation entry anywhere in the *raw* trace fires the combined bad event
- `theorem DuplexSpongeFS.Sponge316.hasInvEntry_implies_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:929](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L929) — **Keystone**: an inverse-permutation entry anywhere in the *raw* trace fires the combined bad event

### `hasInvEntry_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasInvEntry_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:889](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L889) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves `HasInvEntry` (str
- `lemma DuplexSpongeFS.Sponge316.hasInvEntry_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:889](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L889) — **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves `HasInvEntry` (str

### `hasInvKey` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.hasInvKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:344](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L344) — Whether a permutation cache already holds the inverse key `b`.
- `def DuplexSpongeFS.EagerLazyDS.hasInvKey` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:344](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L344) — Whether a permutation cache already holds the inverse key `b`.

### `hasInvKey_foldl_imp` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hasInvKey_foldl_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:451](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L451) — An inverse key present after the whole fold was present at the start or inserted by some entry of th
- `theorem DuplexSpongeFS.EagerLazyDS.hasInvKey_foldl_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:451](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L451) — An inverse key present after the whole fold was present at the start or inserted by some entry of th

### `hasInvKey_stepCache_imp` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hasInvKey_stepCache_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:363](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L363) — One fold step can only create the inverse key it inserts (sound direction only).
- `theorem DuplexSpongeFS.EagerLazyDS.hasInvKey_stepCache_imp` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:363](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L363) — One fold step can only create the inverse key it inserts (sound direction only).

### `hasPermCapacityBeforeForwardOutputPaper_of_first` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L287) — Forgetting the first-occurrence guard leaves the broad paper shape.
- `theorem DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:287](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L287) — Forgetting the first-occurrence guard leaves the broad paper shape.

### `hasPermCapacityBeforeForwardOutputPaper_of_firstPermNat` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_of_firstPermNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:384](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L384) — Convert the natural-index witness back to the broad paper shape.
- `lemma DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_of_firstPermNat` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:384](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L384) — Convert the natural-index witness back to the broad paper shape.

### `hasPermCapacityBeforeForwardOutputPaper_removeRedundant_of_first` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_removeRedundant_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:608](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L608) — **Public dedup bridge (paper semantics)**: a raw first-occurrence perm-capacity collision survives `
- `theorem DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_removeRedundant_of_first` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:608](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L608) — **Public dedup bridge (paper semantics)**: a raw first-occurrence perm-capacity collision survives `

### `hasPriorReversedForwardAnchor_iff_hasRedundantForwardAnchor_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasPriorReversedForwardAnchor_iff_hasRedundantForwardAnchor_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1522](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1522) — Off `E`, the prior-reversed-forward obstruction is exactly the statement that some nonterminal `J_BT
- `theorem DuplexSpongeFS.Sponge316.hasPriorReversedForwardAnchor_iff_hasRedundantForwardAnchor_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1522](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1522) — Off `E`, the prior-reversed-forward obstruction is exactly the statement that some nonterminal `J_BT

### `hasRedundantForwardAnchor_of_prior_reverse` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hasRedundantForwardAnchor_of_prior_reverse` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1468](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1468) — A prior same-direction reversed-forward entry makes the corresponding `J_BT` forward anchor redundan
- `theorem DuplexSpongeFS.Sponge316.hasRedundantForwardAnchor_of_prior_reverse` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1468](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1468) — A prior same-direction reversed-forward entry makes the corresponding `J_BT` forward anchor redundan

### `hashEntry` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.hashEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:338](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L338) — Private shorthand for a concrete hash query-answer entry.
- `def DuplexSpongeFS.Sponge316.hashEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:338](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L338) — Private shorthand for a concrete hash query-answer entry.

### `hashEntryC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.hashEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:54](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L54) — (no docstring)
- `def DuplexSpongeFS.Sponge316.hashEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:54](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L54) — (no docstring)

### `hashEntryD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.hashEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:50](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L50) — (no docstring)
- `def DuplexSpongeFS.Sponge316.hashEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:50](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L50) — (no docstring)

### `hashEntryP` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.hashEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:241](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L241) — (no docstring)
- `def DuplexSpongeFS.Sponge316.hashEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:241](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L241) — (no docstring)

### `hashKey_isSome_foldl_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hashKey_isSome_foldl_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:333](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L333) — A cached hash key stays cached through any fold suffix (`isSome` form).
- `theorem DuplexSpongeFS.EagerLazyDS.hashKey_isSome_foldl_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:333](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L333) — A cached hash key stays cached through any fold suffix (`isSome` form).

### `hashRecord_cached_after_consistent` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hashRecord_cached_after_consistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:283](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L283) — After a consistent hash step, the exact logged hash answer is cached.
- `theorem DuplexSpongeFS.EagerLazyDS.hashRecord_cached_after_consistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:283](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L283) — After a consistent hash step, the exact logged hash answer is cached.

### `hashRecord_take_of_le` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hashRecord_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:162](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L162) — A hash record at the `(j'+1)`-prefix fold persists (with its value) to any larger prefix.
- `theorem DuplexSpongeFS.EagerLazyDS.hashRecord_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:162](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L162) — A hash record at the `(j'+1)`-prefix fold persists (with its value) to any larger prefix.

### `hash_anchor_unique` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.hash_anchor_unique` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:156](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L156) — **U2 (anchor uniqueness, paper event)**: off `EPaper`, two hash anchors with equal answer capacities
- `theorem DuplexSpongeFS.Paper.hash_anchor_unique` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:156](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L156) — **U2 (anchor uniqueness, paper event)**: off `EPaper`, two hash anchors with equal answer capacities

### `hash_anchor_unique_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hash_anchor_unique_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:473](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L473) — Off `BadEventDSPaper.E`, two hash anchors with equal answer capacities carry the same statement.
- `theorem DuplexSpongeFS.Sponge316.hash_anchor_unique_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:473](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L473) — Off `BadEventDSPaper.E`, two hash anchors with equal answer capacities carry the same statement.

### `hash_entry_fresh` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hash_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1221](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1221) — **A non-redundant hash entry is fresh.** A consistent hash hit forces the cached answer to equal the
- `theorem DuplexSpongeFS.EagerLazyDS.hash_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1221](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1221) — **A non-redundant hash entry is fresh.** A consistent hash hit forces the cached answer to equal the

### `hash_fresh_ans_new` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.hash_fresh_ans_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:574](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L574) — A fresh hash step that is not an anchored collision yields an answer that is not an existing slot.
- `theorem DuplexSpongeFS.EagerLazyDS.hash_fresh_ans_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:574](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L574) — A fresh hash step that is not an anchored collision yields an answer that is not an existing slot.

### `hash_step_separation` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.hash_step_separation` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L122) — **U3 (anchor separation, paper event)**: off `EPaper`, no chain-step output capacity equals a hash-a
- `theorem DuplexSpongeFS.Paper.hash_step_separation` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L122) — **U3 (anchor separation, paper event)**: off `EPaper`, no chain-step output capacity equals a hash-a

### `hash_step_separation_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.hash_step_separation_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:388](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L388) — Off `BadEventDSPaper.E`, a hash anchor capacity cannot occur as the answer capacity of a family chai
- `theorem DuplexSpongeFS.Sponge316.hash_step_separation_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:388](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L388) — Off `BadEventDSPaper.E`, a hash anchor capacity cannot occur as the answer capacity of a family chai

### `hbig_radical_of_coeff_budget` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.hbig_radical_of_coeff_budget` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:210](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L210) — **The assembler-shaped `hbig` at the RADICAL certificate** — the exact counting field of `ofProducer
- `theorem ArkLib.RadicalWire304.hbig_radical_of_coeff_budget` [ArkLib/ToMathlib/RadicalAssembler.lean:229](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L229) — **The assembler-shaped `hbig` at the RADICAL certificate** — the exact counting field of `ofProducer

### `hbig_radical_of_hbig_fiber` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.hbig_radical_of_hbig_fiber` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:249](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L249) — **The overlap-regime budget transfer**: wherever the FIBER certificate is nonzero (the regime in whi
- `theorem ArkLib.RadicalWire304.hbig_radical_of_hbig_fiber` [ArkLib/ToMathlib/RadicalAssembler.lean:268](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L268) — **The overlap-regime budget transfer**: wherever the FIBER certificate is nonzero (the regime in whi

### `hbr_canonical_radical` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.hbr_canonical_radical` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:135](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L135) — **K4 branch certificate (`hbr` at the radical canonical cofactor)** from the single §6-incidence fac
- `theorem ArkLib.RadicalWire304.hbr_canonical_radical` [ArkLib/ToMathlib/RadicalAssembler.lean:154](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L154) — **K4 branch certificate (`hbr` at the radical canonical cofactor)** from the single §6-incidence fac

### `hcoeffPoly_witness_of_producersOn_radical` (2 declarations, 2 files)

- `theorem ArkLib.RootOn304.hcoeffPoly_witness_of_producersOn_radical` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:593](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L593) — **THE RADICAL FRONT DOOR**: the root-free `hcoeffPoly` existential from the radical producers.  Vers
- `theorem ArkLib.RootOn304.hcoeffPoly_witness_of_producersOn_radical` [ArkLib/ToMathlib/RadicalAssembler.lean:612](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L612) — **THE RADICAL FRONT DOOR**: the root-free `hcoeffPoly` existential from the radical producers.  Vers

### `hcoeffPoly_witness_of_producersOn_radical_sep` (2 declarations, 2 files)

- `theorem ArkLib.RootOn304.hcoeffPoly_witness_of_producersOn_radical_sep` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:635](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L635) — The `hRsep` drop-in form of the radical front door (exact hypothesis-list parity with `hcoeffPoly_wi
- `theorem ArkLib.RootOn304.hcoeffPoly_witness_of_producersOn_radical_sep` [ArkLib/ToMathlib/RadicalAssembler.lean:654](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L654) — The `hRsep` drop-in form of the radical front door (exact hypothesis-list parity with `hcoeffPoly_wi

### `headBorderEdges` (2 declarations, 2 files)

- `def AGL24.headBorderEdges` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:60](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L60) — The cut-crossing edges whose current orientation head lies in `T`.
- `def AGL24.headBorderEdges` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:36](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L36) — The cut-crossing edges whose current orientation head lies in `T`.

### `headBorderEdges_card_le_borderEdges_card` (2 declarations, 2 files)

- `theorem AGL24.headBorderEdges_card_le_borderEdges_card` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:91](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L91) — (no docstring)
- `theorem AGL24.headBorderEdges_card_le_borderEdges_card` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:75](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L75) — (no docstring)

### `headBorderEdges_card_updateHead_eq_succ` (2 declarations, 2 files)

- `theorem AGL24.headBorderEdges_card_updateHead_eq_succ` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:123](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L123) — (no docstring)
- `theorem AGL24.headBorderEdges_card_updateHead_eq_succ` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:128](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L128) — (no docstring)

### `headBorderEdges_subset_borderEdges` (2 declarations, 2 files)

- `theorem AGL24.headBorderEdges_subset_borderEdges` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:82](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L82) — (no docstring)
- `theorem AGL24.headBorderEdges_subset_borderEdges` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:66](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L66) — (no docstring)

### `head_some` (2 declarations, 2 files)

- `lemma CheckClaim.head_some` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:76](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L76) — A simulated `some`-wrapped computation only outputs `some`.
- `lemma CheckClaim.head_some` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:84](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L84) — A simulated `some`-wrapped computation only outputs `some`.

### `honestBad_birthday_unconditional` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.BirthdayBoundPaper.honestBad_birthday_unconditional` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean#L52) — **The §5.6 → §5.8 channel, unconditional**: the honest bad events of the eager `D_𝔖`-carrier game ob
- `theorem DuplexSpongeFS.BirthdayBoundPaper.honestBad_birthday_unconditional` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean:52](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean#L52) — **The §5.6 → §5.8 channel, unconditional**: the honest bad events of the eager `D_𝔖`-carrier game ob

### `honestBad_claim5_21Bound_unconditional` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.BirthdayBoundPaper.honestBad_claim5_21Bound_unconditional` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean#L68) — **Claim 5.21, unconditional**: at the CO25 trace length `T = tₕ + 1 + tₚ + L + tₚᵢ`, the honest bad
- `theorem DuplexSpongeFS.BirthdayBoundPaper.honestBad_claim5_21Bound_unconditional` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean#L68) — **Claim 5.21, unconditional**: at the CO25 trace length `T = tₕ + 1 + tₚ + L + tₚᵢ`, the honest bad

### `hx_of_global_structural_radical` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.hx_of_global_structural_radical` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:423](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L423) — **Per-place `ξ`-nonvanishing at the radical decoded roots, GLOBALLY discharged** — mirror of `RootOn
- `theorem ArkLib.RadicalWire304.hx_of_global_structural_radical` [ArkLib/ToMathlib/RadicalAssembler.lean:442](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L442) — **Per-place `ξ`-nonvanishing at the radical decoded roots, GLOBALLY discharged** — mirror of `RootOn

### `index_entry_forward_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.index_entry_forward_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:291](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L291) — **The cascade (the mathematical core of CO25 Lemmas 5.12/5.16)**: off the combined paper bad event,
- `theorem DuplexSpongeFS.Sponge316.index_entry_forward_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:291](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L291) — **The cascade (the mathematical core of CO25 Lemmas 5.12/5.16)**: off the combined paper bad event,

### `index_step1` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.index_step1` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:130](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L130) — The chain index of step 1 (pair `(sA, sB)`) is the raw slot `3`.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.index_step1` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:130](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L130) — The chain index of step 1 (pair `(sA, sB)`) is the raw slot `3`.

### `index_step2` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.index_step2` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:150](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L150) — The chain index of step 2 (pair `(sa, sb)`) is the raw slot `1`.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.index_step2` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:150](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L150) — The chain index of step 2 (pair `(sa, sb)`) is the raw slot `1`.

### `inv_entry_fresh` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.inv_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:874](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L874) — **A non-redundant inverse entry is fresh.**
- `theorem DuplexSpongeFS.EagerLazyDS.inv_entry_fresh` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:874](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L874) — **A non-redundant inverse entry is fresh.**

### `inv_fresh_cap_new` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.inv_fresh_cap_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:563](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L563) — A fresh inverse step that is not an anchored collision yields an answer capacity that is neither an
- `theorem DuplexSpongeFS.EagerLazyDS.inv_fresh_cap_new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:563](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L563) — A fresh inverse step that is not an anchored collision yields an answer capacity that is neither an

### `inv_hit_sameClass_mem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.inv_hit_sameClass_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:800](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L800) — **Piece (A2c), inverse arm**: in a fold from empty over `L`, a consistent inverse entry `⟨inr (inr b
- `theorem DuplexSpongeFS.EagerLazyDS.inv_hit_sameClass_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:800](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L800) — **Piece (A2c), inverse arm**: in a fold from empty over `L`, a consistent inverse entry `⟨inr (inr b

### `inverseEntryC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.inverseEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:62](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L62) — (no docstring)
- `def DuplexSpongeFS.Sponge316.inverseEntryC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:62](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L62) — (no docstring)

### `inverseEntryD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.inverseEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L58) — (no docstring)
- `def DuplexSpongeFS.Sponge316.inverseEntryD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:58](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L58) — (no docstring)

### `inverseEntryP` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.inverseEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:249](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L249) — (no docstring)
- `def DuplexSpongeFS.Sponge316.inverseEntryP` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:249](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L249) — (no docstring)

### `isTotalQueryBound_P` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge314.K1.isTotalQueryBound_P` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L77) — `P` makes exactly one query.
- `lemma DuplexSpongeFS.Sponge314.K1.isTotalQueryBound_P` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L77) — `P` makes exactly one query.

### `jbt_hash_firstOfClassAt''` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_hash_firstOfClassAt''` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:158](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L158) — **Bridge**: the `J_BT` hash slot is first-of-mirror-class (hash entries are self-mirrors).
- `theorem DuplexSpongeFS.Paper.jbt_hash_firstOfClassAt''` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:158](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L158) — **Bridge**: the `J_BT` hash slot is first-of-mirror-class (hash entries are self-mirrors).

### `jbt_hash_getElem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.jbt_hash_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:977](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L977) — `J_BT` hash-index payloads point to the recorded hash query for their sequence.
- `theorem DuplexSpongeFS.Sponge316.jbt_hash_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:977](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L977) — `J_BT` hash-index payloads point to the recorded hash query for their sequence.

### `jbt_hash_getElem''` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_hash_getElem''` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:140](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L140) — The `J_BT` hash slot carries the hash anchor (Fin-getElem normal form).
- `theorem DuplexSpongeFS.Paper.jbt_hash_getElem''` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:140](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L140) — The `J_BT` hash slot carries the hash anchor (Fin-getElem normal form).

### `jbt_hash_no_prior` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.jbt_hash_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:999](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L999) — A `J_BT` hash-index payload is the first occurrence of its hash anchor: no strictly earlier raw trac
- `theorem DuplexSpongeFS.Sponge316.jbt_hash_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:999](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L999) — A `J_BT` hash-index payload is the first occurrence of its hash anchor: no strictly earlier raw trac

### `jbt_hash_not_redundant` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.jbt_hash_not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1056](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1056) — The hash index carried by any `J_BT` payload is not itself removed by one step of the duplex-sponge
- `theorem DuplexSpongeFS.Sponge316.jbt_hash_not_redundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1056](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1056) — The hash index carried by any `J_BT` payload is not itself removed by one step of the duplex-sponge

### `jbt_perm_forward_getElem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.jbt_perm_forward_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1151](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1151) — Off `E`, a nonterminal `J_BT` permutation-index payload points to the forward permutation query for
- `theorem DuplexSpongeFS.Sponge316.jbt_perm_forward_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1151](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1151) — Off `E`, a nonterminal `J_BT` permutation-index payload points to the forward permutation query for

### `jbt_perm_getElem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_perm_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:61](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L61) — Unconditional either-direction payload of a nonterminal `J_BT` permutation index (local copy of the
- `theorem DuplexSpongeFS.Paper.jbt_perm_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:61](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L61) — Unconditional either-direction payload of a nonterminal `J_BT` permutation index (local copy of the

### `jbt_perm_no_prior_of_lt` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.jbt_perm_no_prior_of_lt` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1174](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1174) — A nonterminal `J_BT` permutation-index payload is the first occurrence of either recorded permutatio
- `theorem DuplexSpongeFS.Sponge316.jbt_perm_no_prior_of_lt` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1174](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1174) — A nonterminal `J_BT` permutation-index payload is the first occurrence of either recorded permutatio

### `jbt_perm_slot_cases'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_cases'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:99](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L99) — The raw-trace entry at a nonterminal `J_BT` permutation index is the forward or the inverse form of
- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_cases'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:99](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L99) — The raw-trace entry at a nonterminal `J_BT` permutation index is the forward or the inverse form of

### `jbt_perm_slot_firstOfClassAt'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_firstOfClassAt'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L122) — **Bridge**: a nonterminal `J_BT` permutation slot is first-of-mirror-class (`M2Engine.FirstOfClassAt
- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_firstOfClassAt'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L122) — **Bridge**: a nonterminal `J_BT` permutation slot is first-of-mirror-class (`M2Engine.FirstOfClassAt

### `jbt_perm_slot_lt'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_lt'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L85) — A nonterminal `J_BT` permutation index is a genuine raw-trace index.
- `theorem DuplexSpongeFS.Paper.jbt_perm_slot_lt'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L85) — A nonterminal `J_BT` permutation index is a genuine raw-trace index.

### `jbt_time_h_first_perm_forward_getElem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.jbt_time_h_first_perm_forward_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1237](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1237) — Off `E`, the first chain index in a hash-after-first-permutation `J_BT` payload is the forward permu
- `theorem DuplexSpongeFS.Sponge316.jbt_time_h_first_perm_forward_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1237](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1237) — Off `E`, the first chain index in a hash-after-first-permutation `J_BT` payload is the forward permu

### `jbt_time_h_outputState_nonempty` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.jbt_time_h_outputState_nonempty` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1202](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1202) — A `J_BT` payload witnessing the hash-after-first-permutation timing condition cannot be the empty ch
- `theorem DuplexSpongeFS.Sponge316.jbt_time_h_outputState_nonempty` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1202](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1202) — A `J_BT` payload witnessing the hash-after-first-permutation timing condition cannot be the empty ch

### `jbt_time_p_next_outputState_bound` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.jbt_time_p_next_outputState_bound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1264](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1264) — In an `E_time_p_honest` witness, the successor pair index cannot be the terminal sentinel: otherwise
- `theorem DuplexSpongeFS.Sponge316.jbt_time_p_next_outputState_bound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1264](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1264) — In an `E_time_p_honest` witness, the successor pair index cannot be the terminal sentinel: otherwise

### `johnsonDenom` (2 declarations, 2 files)

- `def ArkLib.JohnsonBound.johnsonDenom` [ArkLib/Data/CodingTheory/JohnsonBound/ListSize.lean:159](../../../ArkLib/Data/CodingTheory/JohnsonBound/ListSize.lean#L159) — The **Johnson denominator** `(n - e)² - n·(n - d)`. The Johnson regime is where it is positive.
- `def ArkLib.JohnsonBound.johnsonDenom` [ArkLib/Data/CodingTheory/ProximityGap/JohnsonCommonCenterRefutation.lean:11](../../../ArkLib/Data/CodingTheory/ProximityGap/JohnsonCommonCenterRefutation.lean#L11) — (no docstring)

### `key_cached_after_step_hash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:213](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L213) — After folding any entry, that entry's key is cached (fresh ⟹ created; hit ⟹ was there). The work-ord
- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:213](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L213) — After folding any entry, that entry's key is cached (fresh ⟹ created; hit ⟹ was there). The work-ord

### `key_cached_after_step_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:221](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L221) — After folding a forward entry, its forward key is cached.
- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:221](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L221) — After folding a forward entry, its forward key is cached.

### `key_cached_after_step_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:232](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L232) — After folding an inverse entry, its value key is cached.
- `theorem DuplexSpongeFS.EagerLazyDS.key_cached_after_step_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:232](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L232) — After folding an inverse entry, its value key is cached.

### `lazyDSImplFlagged` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L68) — The ghost-flagged lazy combined oracle: run `lazyDSImpl` verbatim and accumulate, as a `Prop` state
- `def DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:68](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L68) — The ghost-flagged lazy combined oracle: run `lazyDSImpl` verbatim and accumulate, as a `Prop` state

### `lazyDSImplFlagged_flag_monotone` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_flag_monotone` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:125](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L125) — The flag is sticky: once set, every reachable successor state keeps it.
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_flag_monotone` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:125](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L125) — The flag is sticky: once set, every reachable successor state keeps it.

### `lazyDSImplFlagged_run` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_run` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L77) — Single-step exposure of the flagged oracle (public; the defeq `show` does not transport across files
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_run` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L77) — Single-step exposure of the flagged oracle (public; the defeq `show` does not transport across files

### `lazyDSImplFlagged_step_bad` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_bad` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L300) — **The engine's `hstep_bad`**: from an unflagged state with cache size `m`, one step flags with proba
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_bad` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L300) — **The engine's `hstep_bad`**: from an unflagged state with cache size `m`, one step flags with proba

### `lazyDSImplFlagged_step_size` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_size` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L114) — The engine's `hstep_size` for the flagged carrier: the cache component grows by at most one per step
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_size` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L114) — The engine's `hstep_size` for the flagged carrier: the cache component grows by at most one per step

### `lazyDSImplFlagged_step_support` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_support` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L84) — **The per-step support facts**: each reachable one-step outcome of the flagged oracle has the folded
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_support` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L84) — **The per-step support facts**: each reachable one-step outcome of the flagged oracle has the folded

### `lazyDSImpl_run_map_flagged` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImpl_run_map_flagged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L85) — **The forgetting bridge**: the plain lazy run is the state projection of the flagged run — the ghost
- `theorem DuplexSpongeFS.EagerLazyDS.lazyDSImpl_run_map_flagged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:85](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L85) — **The forgetting bridge**: the plain lazy run is the state projection of the flagged run — the ghost

### `le_length_unusedKeysList` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.le_length_unusedKeysList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:202](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L202) — The unused-keys pool keeps at least `\|X\| - \|cache\|` elements.
- `lemma DuplexSpongeFS.EagerLazyDS.le_length_unusedKeysList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:202](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L202) — The unused-keys pool keeps at least `\|X\| - \|cache\|` elements.

### `le_length_unusedValuesList` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.le_length_unusedValuesList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L184) — The unused-values pool keeps at least `\|X\| - \|cache\|` elements.
- `lemma DuplexSpongeFS.EagerLazyDS.le_length_unusedValuesList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L184) — The unused-values pool keeps at least `\|X\| - \|cache\|` elements.

### `lemma512Paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.lemma512Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean:137](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaper.lean#L137) — **CO25 Lemma 5.12 (paper event)**: off the paper-faithful bad event `EPaper`, no BackTrack chain ste
- `theorem DuplexSpongeFS.Paper.lemma512Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean:137](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Paper.lean#L137) — **CO25 Lemma 5.12 (paper event)**: off the paper-faithful bad event `EPaper`, no BackTrack chain ste

### `lemma514Paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.lemma514Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:275](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L275) — **CO25 Lemma 5.14 over the paper event** (M2b, Def-5.5/Eq-26-faithful): off `EPaper` the backtrack f
- `theorem DuplexSpongeFS.Paper.lemma514Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:275](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L275) — **CO25 Lemma 5.14 over the paper event** (M2b, Def-5.5/Eq-26-faithful): off `EPaper` the backtrack f

### `lemma516HashPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.lemma516HashPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:260](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L260) — **Lemma 5.16, hash half (paper event)**: off `EPaper`, the anchoring hash query does not appear afte
- `theorem DuplexSpongeFS.Paper.lemma516HashPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:260](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L260) — **Lemma 5.16, hash half (paper event)**: off `EPaper`, the anchoring hash query does not appear afte

### `lemma516Paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.lemma516Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:351](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L351) — **CO25 Lemma 5.16 over the paper bad event**: off `EPaper`, all BackTrack chain queries appear in tr
- `theorem DuplexSpongeFS.Paper.lemma516Paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:351](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L351) — **CO25 Lemma 5.16 over the paper bad event**: off `EPaper`, all BackTrack chain queries appear in tr

### `lemma516TimePPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.lemma516TimePPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean:295](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashPaper.lean#L295) — **Lemma 5.16, permutation half (paper event)**: off `EPaper`, no chain permutation query appears in
- `theorem DuplexSpongeFS.Paper.lemma516TimePPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean:295](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516Paper.lean#L295) — **Lemma 5.16, permutation half (paper event)**: off `EPaper`, no chain permutation query appears in

### `lemma58StepBound` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.lemma58StepBound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:243](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L243) — The per-step bad probability: `(2m+1)·\|U\|^R / (\|U\|^N − m)` from cache size `m` — the union bound ove
- `def DuplexSpongeFS.EagerLazyDS.lemma58StepBound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:243](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L243) — The per-step bad probability: `(2m+1)·\|U\|^R / (\|U\|^N − m)` from cache size `m` — the union bound ove

### `lemma58StepBound_monotone` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.lemma58StepBound_monotone` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L248) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.lemma58StepBound_monotone` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L248) — (no docstring)

### `lemma58_num_ne_zero` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.lemma58_num_ne_zero` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:257](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L257) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.lemma58_num_ne_zero` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:257](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L257) — (no docstring)

### `lemma5_12HonestResidualPaper_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_12HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:441](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L441) — The residual `Lemma5_12HonestResidualPaper`, discharged.
- `theorem DuplexSpongeFS.Sponge316.lemma5_12HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:441](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L441) — The residual `Lemma5_12HonestResidualPaper`, discharged.

### `lemma5_12_honest` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_12_honest` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1870](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1870) — **M2a discharged** — `DuplexSpongeFS.KeyLemmaFoundations.Lemma5_12HonestResidual` holds: off the com
- `theorem DuplexSpongeFS.Sponge316.lemma5_12_honest` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1870](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1870) — **M2a discharged** — `DuplexSpongeFS.KeyLemmaFoundations.Lemma5_12HonestResidual` holds: off the com

### `lemma5_12_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_12_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:425](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L425) — **CO25 Lemma 5.12, paper semantics — DISCHARGED**: off the paper combined bad event, no BackTrack ch
- `theorem DuplexSpongeFS.Sponge316.lemma5_12_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:425](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L425) — **CO25 Lemma 5.12, paper semantics — DISCHARGED**: off the paper combined bad event, no BackTrack ch

### `lemma5_14HonestResidualPaper_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_14HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:705](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L705) — The residual `Lemma5_14HonestResidualPaper`, discharged.
- `theorem DuplexSpongeFS.Sponge316.lemma5_14HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:705](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L705) — The residual `Lemma5_14HonestResidualPaper`, discharged.

### `lemma5_14HonestResidual_false` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.ForkCounter.lemma5_14HonestResidual_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:594](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L594) — **The in-tree `Lemma5_14HonestResidual` is FALSE** (at `StmtIn := Unit`, `U := UInt8`, sponge width
- `theorem DuplexSpongeFS.Sponge316.ForkCounter.lemma5_14HonestResidual_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:594](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L594) — **The in-tree `Lemma5_14HonestResidual` is FALSE** (at `StmtIn := Unit`, `U := UInt8`, sponge width

### `lemma5_14_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_14_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:629](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L629) — **CO25 Lemma 5.14, paper semantics — DISCHARGED**: off `BadEventDSPaper.E`, the backtrack family has
- `theorem DuplexSpongeFS.Sponge316.lemma5_14_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:629](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L629) — **CO25 Lemma 5.14, paper semantics — DISCHARGED**: off `BadEventDSPaper.E`, the backtrack family has

### `lemma5_16HonestResidualPaper_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:508](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L508) — The residual `Lemma5_16HonestResidualPaper`, discharged.
- `theorem DuplexSpongeFS.Sponge316.lemma5_16HonestResidualPaper_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:508](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L508) — The residual `Lemma5_16HonestResidualPaper`, discharged.

### `lemma5_16HonestResidual_false` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.TimePCounter.lemma5_16HonestResidual_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:502](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L502) — **The in-tree `Lemma5_16HonestResidual` is FALSE** (at `StmtIn := Unit`, `U := UInt8`, sponge width
- `theorem DuplexSpongeFS.Sponge316.TimePCounter.lemma5_16HonestResidual_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:502](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L502) — **The in-tree `Lemma5_16HonestResidual` is FALSE** (at `StmtIn := Unit`, `U := UInt8`, sponge width

### `lemma5_16_honest_hash_half` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16_honest_hash_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HashHalf.lean#L234) — **M2c, hash half** — CO25 Lemma 5.16, `E_{time,h}` side: off the combined bad event `E`, no backtrac
- `theorem DuplexSpongeFS.Sponge316.lemma5_16_honest_hash_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516HashHalf.lean#L234) — **M2c, hash half** — CO25 Lemma 5.16, `E_{time,h}` side: off the combined bad event `E`, no backtrac

### `lemma5_16_honest_of_noRedundantEntryDS` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16_honest_of_noRedundantEntryDS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1858](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1858) — Conditional full M2c assembly for traces that are already deduplicated. This is the direct target if
- `theorem DuplexSpongeFS.Sponge316.lemma5_16_honest_of_noRedundantEntryDS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1858](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1858) — Conditional full M2c assembly for traces that are already deduplicated. This is the direct target if

### `lemma5_16_honest_of_no_prior_reverse` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16_honest_of_no_prior_reverse` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1826](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1826) — Conditional full M2c assembly: a global exclusion of the prior reversed-forward obstruction is enoug
- `theorem DuplexSpongeFS.Sponge316.lemma5_16_honest_of_no_prior_reverse` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1826](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1826) — Conditional full M2c assembly: a global exclusion of the prior reversed-forward obstruction is enoug

### `lemma5_16_honest_of_no_redundant_forward_anchor` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16_honest_of_no_redundant_forward_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1842](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1842) — Conditional full M2c assembly, phrased at the stronger dedup-invariant boundary: excluding redundant
- `theorem DuplexSpongeFS.Sponge316.lemma5_16_honest_of_no_redundant_forward_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1842](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1842) — Conditional full M2c assembly, phrased at the stronger dedup-invariant boundary: excluding redundant

### `lemma5_16_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:497](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L497) — **CO25 Lemma 5.16, paper semantics — DISCHARGED** (both halves): off the paper combined bad event, a
- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:497](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L497) — **CO25 Lemma 5.16, paper semantics — DISCHARGED** (both halves): off the paper combined bad event, a

### `lemma5_16_paper_hash_half` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper_hash_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:1011](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L1011) — **CO25 Lemma 5.16, hash half, paper semantics — DISCHARGED**: off the paper combined bad event, no b
- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper_hash_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:1011](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L1011) — **CO25 Lemma 5.16, hash half, paper semantics — DISCHARGED**: off the paper combined bad event, no b

### `lemma5_16_paper_time_p_half` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper_time_p_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:452](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L452) — **CO25 Lemma 5.16, permutation half, paper semantics — DISCHARGED**: off the paper combined bad even
- `theorem DuplexSpongeFS.Sponge316.lemma5_16_paper_time_p_half` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:452](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L452) — **CO25 Lemma 5.16, permutation half, paper semantics — DISCHARGED**: off the paper combined bad even

### `lemma5_8Bound_one_lt_one` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge314.K1.lemma5_8Bound_one_lt_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:128](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L128) — The claimed CO25 Lemma 5.8 bound at `T = 1` is `4/(2·256) < 1`.
- `lemma DuplexSpongeFS.Sponge314.K1.lemma5_8Bound_one_lt_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:128](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L128) — The claimed CO25 Lemma 5.8 bound at `T = 1` is `4/(2·256) < 1`.

### `lemma5_8EagerBirthdayResidual_false` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge314.K1.lemma5_8EagerBirthdayResidual_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:147](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L147) — **#314 K1 — the eager birthday residual is FALSE as stated** (at `StmtIn := Unit`, `U := UInt8`, spo
- `theorem DuplexSpongeFS.Sponge314.K1.lemma5_8EagerBirthdayResidual_false` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:147](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L147) — **#314 K1 — the eager birthday residual is FALSE as stated** (at `StmtIn := Unit`, `U := UInt8`, spo

### `lemma5_8EagerPaperResidual_holds` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.BirthdayBoundPaper.lemma5_8EagerPaperResidual_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Reduction.lean#L46) — **The repaired Lemma 5.8 eager residual holds**: the lazy-side bound `probEvent_EPaper_toReal_le_lem
- `theorem DuplexSpongeFS.BirthdayBoundPaper.lemma5_8EagerPaperResidual_holds` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Reduction.lean#L46) — **The repaired Lemma 5.8 eager residual holds**: the lazy-side bound `probEvent_EPaper_toReal_le_lem

### `length_not_lt` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.length_not_lt` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:244](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L244) — Asymmetric length kill: a strictly shorter family sequence would put its hash-anchor capacity on a c
- `theorem DuplexSpongeFS.Paper.length_not_lt` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:244](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L244) — Asymmetric length kill: a strictly shorter family sequence would put its hash-anchor capacity on a c

### `length_not_lt_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.length_not_lt_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:599](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L599) — Asymmetric length kill: a strictly shorter family sequence would put its hash-anchor capacity on a c
- `theorem DuplexSpongeFS.Sponge316.length_not_lt_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:599](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L599) — Asymmetric length kill: a strictly shorter family sequence would put its hash-anchor capacity on a c

### `listPoly` (2 declarations, 2 files)

- `def Whir302SZ.listPoly` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:25](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L25) — The polynomial whose Horner evaluation is `listEval`.
- `def Whir302SZ.listPoly` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:98](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L98) — The polynomial whose Horner evaluation is `listEval`.

### `listPoly_cons` (2 declarations, 2 files)

- `theorem Whir302SZ.listPoly_cons` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:37](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L37) — (no docstring)
- `theorem Whir302SZ.listPoly_cons` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:110](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L110) — (no docstring)

### `listPoly_eval` (2 declarations, 2 files)

- `theorem Whir302SZ.listPoly_eval` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:28](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L28) — (no docstring)
- `theorem Whir302SZ.listPoly_eval` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:101](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L101) — (no docstring)

### `listPoly_natDegree_lt` (2 declarations, 2 files)

- `theorem Whir302SZ.listPoly_natDegree_lt` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:40](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L40) — (no docstring)
- `theorem Whir302SZ.listPoly_natDegree_lt` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:113](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L113) — (no docstring)

### `list_split_at` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.list_split_at` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:889](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L889) — A list splits at any in-range position into prefix, element, suffix.
- `theorem DuplexSpongeFS.EagerLazyDS.list_split_at` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:889](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L889) — A list splits at any in-range position into prefix, element, suffix.

### `mcaPrizeLatticeResolved_with_spec_and_adjacent_brackets_of_with_spec` (2 declarations, 2 files)

- `theorem ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_adjacent_brackets_of_with_spec` [ArkLib/Data/CodingTheory/ProximityGap/LineDecodingSpec.lean:1487](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecodingSpec.lean#L1487) — Add the immediate lower and adjacent upper lattice brackets to a concrete adjacent `mcaPrizeLatticeR
- `theorem ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_and_adjacent_brackets_of_with_spec` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSLatticeSpec.lean:882](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSLatticeSpec.lean#L882) — Add the immediate lower and adjacent upper lattice brackets to a concrete adjacent `mcaPrizeLatticeR

### `mem_headBorderEdges` (2 declarations, 2 files)

- `theorem AGL24.mem_headBorderEdges` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:76](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L76) — (no docstring)
- `theorem AGL24.mem_headBorderEdges` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:42](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L42) — (no docstring)

### `mem_headBorderEdges_updateHead_iff` (2 declarations, 2 files)

- `theorem AGL24.mem_headBorderEdges_updateHead_iff` [ArkLib/Data/CodingTheory/AGL24CutSupply.lean:110](../../../ArkLib/Data/CodingTheory/AGL24CutSupply.lean#L110) — (no docstring)
- `theorem AGL24.mem_headBorderEdges_updateHead_iff` [ArkLib/Data/CodingTheory/AGL24Submodular.lean:115](../../../ArkLib/Data/CodingTheory/AGL24Submodular.lean#L115) — (no docstring)

### `mem_imp_sameClass_mem_removeRedundant` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_imp_sameClass_mem_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:470](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L470) — **Dedup is a system of class representatives**: every entry of the raw log has a class-representativ
- `theorem DuplexSpongeFS.EagerLazyDS.mem_imp_sameClass_mem_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:470](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L470) — **Dedup is a system of class representatives**: every entry of the raw log has a class-representativ

### `mem_of_mem_removeRedundantEntryDSPaper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_of_mem_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:608](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L608) — Every entry of the dedup'd base trace was already an entry of the original log.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_of_mem_removeRedundantEntryDSPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:608](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L608) — Every entry of the dedup'd base trace was already an entry of the original log.

### `mem_slotList_foldl_of_mem_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_foldl_of_mem_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:646](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L646) — A capacity cached early stays a slot of every later fold cache.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_foldl_of_mem_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:646](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L646) — A capacity cached early stays a slot of every later fold cache.

### `mem_slotList_of_hash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L234) — A cached hash answer is a slot.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:234](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L234) — A cached hash answer is a slot.

### `mem_slotList_of_hash_cached` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_hash_cached` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1302](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1302) — A cached hash answer is a slot.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_hash_cached` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1302](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1302) — A cached hash answer is a slot.

### `mem_slotList_of_mem_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_mem_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:637](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L637) — Both capacities of a cached permutation pair are slots.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_mem_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:637](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L637) — Both capacities of a cached permutation pair are slots.

### `mem_slotList_of_pair_fst` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_pair_fst` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:246](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L246) — A cached pair's forward-key capacity is a slot.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_pair_fst` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:246](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L246) — A cached pair's forward-key capacity is a slot.

### `mem_slotList_of_pair_snd` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_pair_snd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:255](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L255) — A cached pair's value capacity is a slot.
- `theorem DuplexSpongeFS.EagerLazyDS.mem_slotList_of_pair_snd` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:255](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L255) — A cached pair's value capacity is a slot.

### `mem_support_pure_eq` (2 declarations, 2 files)

- `lemma CheckClaim.mem_support_pure_eq` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:98](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L98) — Membership in the support of a `pure` pins the value. Applied (defeq-unified) against computations t
- `lemma CheckClaim.mem_support_pure_eq` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:106](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L106) — Membership in the support of a `pure` pins the value. Applied (defeq-unified) against computations t

### `mem_support_pure_optionT` (2 declarations, 2 files)

- `lemma CheckClaim.mem_support_pure_optionT` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:88](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L88) — A simulated `pure (some b)` only outputs `some b`.
- `lemma CheckClaim.mem_support_pure_optionT` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:96](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L96) — A simulated `pure (some b)` only outputs `some b`.

### `mkSt` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TimePCounter.mkSt` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:65](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L65) — (no docstring)
- `def DuplexSpongeFS.Sponge316.TimePCounter.mkSt` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:65](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L65) — (no docstring)

### `mpFin_of_decoded_roots_radical` (2 declarations, 2 files)

- `def ArkLib.RadicalWire304.mpFin_of_decoded_roots_radical` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:476](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L476) — The `hRsep` drop-in form of the radical `mpFin` family (via `MappedSliceSeparability.of_separable`).
- `def ArkLib.RadicalWire304.mpFin_of_decoded_roots_radical` [ArkLib/ToMathlib/RadicalAssembler.lean:495](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L495) — The `hRsep` drop-in form of the radical `mpFin` family (via `MappedSliceSeparability.of_separable`).

### `mpFin_of_decoded_roots_radical_mapped` (2 declarations, 2 files)

- `def ArkLib.RadicalWire304.mpFin_of_decoded_roots_radical_mapped` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:449](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L449) — **The `mpFin` family from the RADICAL split, on the consolidated separability hypothesis** — `Decode
- `def ArkLib.RadicalWire304.mpFin_of_decoded_roots_radical_mapped` [ArkLib/ToMathlib/RadicalAssembler.lean:468](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L468) — **The `mpFin` family from the RADICAL split, on the consolidated separability hypothesis** — `Decode

### `natCast_sub_le_ennreal` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.natCast_sub_le_ennreal` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:253](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L253) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.natCast_sub_le_ennreal` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:253](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L253) — (no docstring)

### `natDegreeY_le` (2 declarations, 2 files)

- `lemma R15.natDegreeY_le` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:311](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L311) — The per-monomial weighted-degree bound forces `deg_Y Q ≤ (D-1)/(k-1)` (for `k ≥ 2`), since the leadi
- `lemma R15.natDegreeY_le` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:311](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L311) — The per-monomial weighted-degree bound forces `deg_Y Q ≤ (D-1)/(k-1)` (for `k ≥ 2`), since the leadi

### `natDegree_radical_cofactor_le` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.natDegree_radical_cofactor_le` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:180](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L180) — **The cofactor degree budget**: the canonical radical cofactor has `Y`-degree at most `natDegree(fib
- `theorem ArkLib.RadicalWire304.natDegree_radical_cofactor_le` [ArkLib/ToMathlib/RadicalAssembler.lean:199](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L199) — **The cofactor degree budget**: the canonical radical cofactor has `Y`-degree at most `natDegree(fib

### `natDegree_radical_fiber_eq_add` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.natDegree_radical_fiber_eq_add` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:160](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L160) — Degree additivity of the canonical radical split (monic case).
- `theorem ArkLib.RadicalWire304.natDegree_radical_fiber_eq_add` [ArkLib/ToMathlib/RadicalAssembler.lean:179](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L179) — Degree additivity of the canonical radical split (monic case).

### `natDegree_radical_fiber_le` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.natDegree_radical_fiber_le` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:84](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L84) — Degree budget: the radical of the fiber has no larger degree than the fiber.
- `theorem ArkLib.RadicalWire304.natDegree_radical_fiber_le` [ArkLib/ToMathlib/RadicalAssembler.lean:103](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L103) — Degree budget: the radical of the fiber has no larger degree than the fiber.

### `noRedundant_pairwise_classDistinct` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.noRedundant_pairwise_classDistinct` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:617](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L617) — A `NoRedundantEntryDSPaper` trace is pairwise class-distinct: no later entry shares a class with any
- `theorem DuplexSpongeFS.EagerLazyDS.noRedundant_pairwise_classDistinct` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:617](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L617) — A `NoRedundantEntryDSPaper` trace is pairwise class-distinct: no later entry shares a class with any

### `noRedundant_raw_no_earlier_sameClass` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.noRedundant_raw_no_earlier_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:947](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L947) — In a `NoRedundant` log, no earlier entry is the same class as a later one (raw `ℕ` positions). The f
- `theorem DuplexSpongeFS.EagerLazyDS.noRedundant_raw_no_earlier_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:947](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L947) — In a `NoRedundant` log, no earlier entry is the same class as a later one (raw `ℕ` positions). The f

### `no_redundant_forward_anchor_of_noRedundantEntryDS` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.no_redundant_forward_anchor_of_noRedundantEntryDS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1610](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1610) — A deduplicated trace has no redundant nonterminal `J_BT` forward anchors.
- `theorem DuplexSpongeFS.Sponge316.no_redundant_forward_anchor_of_noRedundantEntryDS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1610](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1610) — A deduplicated trace has no redundant nonterminal `J_BT` forward anchors.

### `notFunction_data_impossible` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.notFunction_data_impossible` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:116](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L116) — **`E_func` refutation**: on a no-redundancy, consistent list, no forward entry can share its key wit
- `theorem DuplexSpongeFS.EagerLazyDS.notFunction_data_impossible` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:116](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L116) — **`E_func` refutation**: on a no-redundancy, consistent list, no forward entry can share its key wit

### `not_E_trc` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L274) — The combined bad event `E` does NOT fire on the countermodel trace.
- `theorem DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L274) — The combined bad event `E` does NOT fire on the countermodel trace.

### `not_E_trcF` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L365) — The combined bad event `E` does NOT fire on the countermodel trace.
- `theorem DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L365) — The combined bad event `E` does NOT fire on the countermodel trace.

### `not_anchoredFrom_cons` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.not_anchoredFrom_cons` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:544](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L544) — Cons-unfolding of `¬ AnchoredFrom`: no step of `e :: ℓ` is an anchored collision.
- `theorem DuplexSpongeFS.EagerLazyDS.not_anchoredFrom_cons` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:544](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L544) — Cons-unfolding of `¬ AnchoredFrom`: no step of `e :: ℓ` is an anchored collision.

### `not_anchoredFrom_split` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.not_anchoredFrom_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:833](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L833) — `¬ AnchoredFrom` gives non-collision at every split point against the fold cache of the prefix.
- `theorem DuplexSpongeFS.EagerLazyDS.not_anchoredFrom_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:833](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L833) — `¬ AnchoredFrom` gives non-collision at every split point against the fold cache of the prefix.

### `not_e_time_h_honest_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_e_time_h_honest_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1778](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1778) — Hash-timing half of M2c: off the combined bad event `E`, the honest hash out-of-order event cannot o
- `theorem DuplexSpongeFS.Sponge316.not_e_time_h_honest_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1778](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1778) — Hash-timing half of M2c: off the combined bad event `E`, the honest hash out-of-order event cannot o

### `not_e_time_honest_of_not_E_of_noRedundantEntryDS` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_e_time_honest_of_not_E_of_noRedundantEntryDS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1790](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1790) — Full timing closure for a fixed trace that is already deduplicated.
- `theorem DuplexSpongeFS.Sponge316.not_e_time_honest_of_not_E_of_noRedundantEntryDS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1790](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1790) — Full timing closure for a fixed trace that is already deduplicated.

### `not_e_time_honest_removeRedundantEntryDS_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_e_time_honest_removeRedundantEntryDS_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1802](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1802) — Full timing closure on the deduplicated base trace produced by `removeRedundantEntryDS`.
- `theorem DuplexSpongeFS.Sponge316.not_e_time_honest_removeRedundantEntryDS_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1802](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1802) — Full timing closure on the deduplicated base trace produced by `removeRedundantEntryDS`.

### `not_e_time_honest_removeRedundantEntryDS_of_not_E_raw` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_e_time_honest_removeRedundantEntryDS_of_not_E_raw` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1814](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1814) — Full timing closure on the deduplicated base trace, discharged from the raw-trace `¬ E tr` hypothesi
- `theorem DuplexSpongeFS.Sponge316.not_e_time_honest_removeRedundantEntryDS_of_not_E_raw` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1814](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1814) — Full timing closure on the deduplicated base trace, discharged from the raw-trace `¬ E tr` hypothesi

### `not_e_time_p_honest_of_not_E_of_noRedundantEntryDS` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_e_time_p_honest_of_not_E_of_noRedundantEntryDS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1619](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1619) — Permutation-timing closure for traces already satisfying `NoRedundantEntryDS`.
- `theorem DuplexSpongeFS.Sponge316.not_e_time_p_honest_of_not_E_of_noRedundantEntryDS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1619](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1619) — Permutation-timing closure for traces already satisfying `NoRedundantEntryDS`.

### `not_e_time_p_honest_of_not_E_of_no_prior_reverse` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_e_time_p_honest_of_not_E_of_no_prior_reverse` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1585](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1585) — Conditional permutation-timing half of M2c: after excluding the explicit prior reversed forward obst
- `theorem DuplexSpongeFS.Sponge316.not_e_time_p_honest_of_not_E_of_no_prior_reverse` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1585](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1585) — Conditional permutation-timing half of M2c: after excluding the explicit prior reversed forward obst

### `not_e_time_p_honest_of_not_E_of_no_redundant_forward_anchor` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_e_time_p_honest_of_not_E_of_no_redundant_forward_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1600](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1600) — Equivalent conditional permutation-timing half of M2c, phrased directly as the missing dedup invaria
- `theorem DuplexSpongeFS.Sponge316.not_e_time_p_honest_of_not_E_of_no_redundant_forward_anchor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1600](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1600) — Equivalent conditional permutation-timing half of M2c, phrased directly as the missing dedup invaria

### `not_hasFwdKey_of_find` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.not_hasFwdKey_of_find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:663](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L663) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.not_hasFwdKey_of_find` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:663](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L663) — (no docstring)

### `not_hasInvEntry_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_hasInvEntry_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:936](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L936) — Contrapositive form of the keystone.
- `theorem DuplexSpongeFS.Sponge316.not_hasInvEntry_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:936](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L936) — Contrapositive form of the keystone.

### `not_inv_getElem` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_inv_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:944](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L944) — Index form of `not_hasInvEntry_of_not_E`: off `E`, no trace slot can be an inverse permutation entry
- `theorem DuplexSpongeFS.Sponge316.not_inv_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:944](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L944) — Index form of `not_hasInvEntry_of_not_E`: off `E`, no trace slot can be an inverse permutation entry

### `not_mem_fwdKeys_of_cap_not_slot` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.not_mem_fwdKeys_of_cap_not_slot` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:670](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L670) — A state whose capacity is not a slot is not a cached forward key.
- `lemma DuplexSpongeFS.EagerLazyDS.not_mem_fwdKeys_of_cap_not_slot` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:670](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L670) — A state whose capacity is not a slot is not a cached forward key.

### `not_redundantEntryDSPaper_forward_of_no_prior` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDSPaper_forward_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:297](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L297) — A forward slot whose pair has no prior copy in either direction is not paper-redundant: the first-oc
- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDSPaper_forward_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:297](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L297) — A forward slot whose pair has no prior copy in either direction is not paper-redundant: the first-oc

### `not_redundantEntryDSPaper_hash_of_no_prior` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDSPaper_hash_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:686](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L686) — A hash slot that is the first occurrence of its concrete entry is not paper-redundant (the hash cert
- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDSPaper_hash_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:686](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L686) — A hash slot that is the first occurrence of its concrete entry is not paper-redundant (the hash cert

### `not_redundantEntryDS_forward_of_no_prior` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDS_forward_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:566](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L566) — A forward slot with no earlier same-or-reversed forward entry is not redundant under the duplex-spon
- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDS_forward_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:566](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L566) — A forward slot with no earlier same-or-reversed forward entry is not redundant under the duplex-spon

### `not_redundantEntryDS_hash_of_no_prior` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDS_hash_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1022](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1022) — A hash trace slot with no earlier copy of the same hash entry is not redundant under the duplex-spon
- `theorem DuplexSpongeFS.Sponge316.not_redundantEntryDS_hash_of_no_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1022](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1022) — A hash trace slot with no earlier copy of the same hash entry is not redundant under the duplex-spon

### `optionT_bind_pure_some` (2 declarations, 2 files)

- `lemma RingSwitching.SumcheckPhase.optionT_bind_pure_some` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1080](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1080) — `OptionT.bind` of an honest `pure (some a)` reduces to the continuation at `a`. Used to collapse the
- `lemma RingSwitching.SumcheckPhase.optionT_bind_pure_some` [ArkLib/ProofSystem/RingSwitching/SumcheckRoundCompleteness.lean:69](../../../ArkLib/ProofSystem/RingSwitching/SumcheckRoundCompleteness.lean#L69) — `OptionT.bind` of an honest `pure (some a)` reduces to the continuation at `a`. Used to collapse the

### `optionT_liftM_run_add_left'` (2 declarations, 2 files)

- `theorem Reduction.optionT_liftM_run_add_left'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:41](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L41) — Run-characterization of the composite lift (left-inclusion).
- `theorem Reduction.optionT_liftM_run_add_left'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L46) — Run-characterization of the composite lift (left-inclusion).

### `optionT_liftM_run_assoc_path'` (2 declarations, 2 files)

- `theorem Reduction.optionT_liftM_run_assoc_path'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean:48](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/LiftCoherence.lean#L48) — (no docstring)
- `theorem Reduction.optionT_liftM_run_assoc_path'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/RunEqHonest.lean#L53) — (no docstring)

### `pairKey_isSome_foldl_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.pairKey_isSome_foldl_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:341](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L341) — A satisfiable pair-cache predicate stays satisfiable through any fold suffix.
- `theorem DuplexSpongeFS.EagerLazyDS.pairKey_isSome_foldl_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:341](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L341) — A satisfiable pair-cache predicate stays satisfiable through any fold suffix.

### `pairKey_isSome_take_of_le` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.pairKey_isSome_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:98](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L98) — A satisfiable pair predicate at the `(j'+1)`-prefix fold persists to any larger prefix.
- `theorem DuplexSpongeFS.EagerLazyDS.pairKey_isSome_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:98](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L98) — A satisfiable pair predicate at the `(j'+1)`-prefix fold persists to any larger prefix.

### `pairRecord_cached_after_consistent_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_cached_after_consistent_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:293](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L293) — After a consistent forward step, the exact pair `(input, output)` is cached.
- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_cached_after_consistent_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:293](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L293) — After a consistent forward step, the exact pair `(input, output)` is cached.

### `pairRecord_cached_after_consistent_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_cached_after_consistent_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:312](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L312) — After a consistent inverse step, the exact pair `(answer, query)` is cached.
- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_cached_after_consistent_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:312](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L312) — After a consistent inverse step, the exact pair `(answer, query)` is cached.

### `pairRecord_take_of_le` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:174](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L174) — A pair record at the `(j'+1)`-prefix fold persists to any larger prefix.
- `theorem DuplexSpongeFS.EagerLazyDS.pairRecord_take_of_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:174](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L174) — A pair record at the `(j'+1)`-prefix fold persists to any larger prefix.

### `pairUDRClose_of_pairFiberwiseClose` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.pairUDRClose_of_pairFiberwiseClose` [ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean:1086](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean#L1086) — if `d⁽ⁱ⁾(f⁽ⁱ⁾, g⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance), then `d(f⁽ⁱ⁾, g⁽ⁱ⁾) < dᵢ/2` (regular c
- `lemma Binius.BinaryBasefold.pairUDRClose_of_pairFiberwiseClose` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorFar.lean:310](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorFar.lean#L310) — (no docstring)

### `prependRLCTargetWTKS` (2 declarations, 2 files)

- `abbrev Spartan.Spec.Bricks.prependRLCTargetWTKS` [ArkLib/ProofSystem/Spartan/ComposedTightRbrKnowledge.lean:177](../../../ArkLib/ProofSystem/Spartan/ComposedTightRbrKnowledge.lean#L177) — The carried honest RLC-target adapter pinned to the concrete oracle-interface universe used by the r
- `abbrev Spartan.Spec.Bricks.prependRLCTargetWTKS` [ArkLib/ProofSystem/Spartan/TightComposedFull.lean:52](../../../ArkLib/ProofSystem/Spartan/TightComposedFull.lean#L52) — Universe-pinned local alias of the carried RLC-target adapter (mirror of `prependRLCTargetKS`).

### `priorCapWitnessC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.priorCapWitnessC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:103](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L103) — Prior-witness class for the inverse-anchored collision shape: an earlier hash entry whose answer **i
- `def DuplexSpongeFS.Sponge316.priorCapWitnessC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:103](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L103) — Prior-witness class for the inverse-anchored collision shape: an earlier hash entry whose answer **i

### `prior_reverse_of_hasRedundantForwardAnchor_of_not_E` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.prior_reverse_of_hasRedundantForwardAnchor_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:1494](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L1494) — Conversely, off `E`, every redundant `J_BT` forward anchor is redundant for the only reason not alre
- `theorem DuplexSpongeFS.Sponge316.prior_reverse_of_hasRedundantForwardAnchor_of_not_E` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:1494](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L1494) — Conversely, off `E`, every redundant `J_BT` forward anchor is redundant for the only reason not alre

### `probEvent_EPaper_toReal_le_lemma5_8Bound` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1662](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1662) — **CO25 Lemma 5.8, unconditional (eager lazy carrier).** For any `T`-query adversary, the probability
- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1662](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1662) — **CO25 Lemma 5.8, unconditional (eager lazy carrier).** For any `T`-query adversary, the probability

### `probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1622](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1622) — **The eager paper bound, conditional on the dedup reduction.** For any `T`-query adversary, the prob
- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1622](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1622) — **The eager paper bound, conditional on the dedup reduction.** For any `T`-query adversary, the prob

### `probEvent_E_eq_one` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge314.K1.probEvent_E_eq_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean:106](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/EagerFalse.lean#L106) — The combined bad event `E` fires with probability **1** in the eager logged game on the single-inver
- `lemma DuplexSpongeFS.Sponge314.K1.probEvent_E_eq_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean:106](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58EagerFalse.lean#L106) — The combined bad event `E` fires with probability **1** in the eager logged game on the single-inver

### `probEvent_eq_one_of_support_init` (2 declarations, 2 files)

- `lemma CheckClaim.probEvent_eq_one_of_support_init` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:105](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L105) — `OptionT`-level probability-one bridge with sampled initial state: if every output of the underlying
- `lemma CheckClaim.probEvent_eq_one_of_support_init` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:113](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L113) — `OptionT`-level probability-one bridge with sampled initial state: if every output of the underlying

### `probEvent_flag_final_le_sum` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_flag_final_le_sum` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:465](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L465) — **The accumulated flag bound**: a `T`-query computation, run from the empty cache with the flag down
- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_flag_final_le_sum` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:465](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L465) — **The accumulated flag bound**: a `T`-query computation, run from the empty cache with the flag down

### `probEvent_flag_final_toReal_le_lemma5_8Bound` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_flag_final_toReal_le_lemma5_8Bound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:545](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L545) — **The complete engine output for CO25 Lemma 5.8**: the final flag probability of any `T`-query compu
- `theorem DuplexSpongeFS.EagerLazyDS.probEvent_flag_final_toReal_le_lemma5_8Bound` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:545](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L545) — **The complete engine output for CO25 Lemma 5.8**: the final flag probability of any `T`-query compu

### `probEvent_salvage_le` (2 declarations, 2 files)

- `theorem Whir302SZ.probEvent_salvage_le` [ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean:109](../../../ArkLib/ProofSystem/Whir/SchwartzZippelCore.lean#L109) — **The per-round salvage probability bound** (the quantitative WHIR flip estimate): in any game that
- `theorem Whir302SZ.probEvent_salvage_le` [ArkLib/ProofSystem/Whir/SubUnitRbr.lean:180](../../../ArkLib/ProofSystem/Whir/SubUnitRbr.lean#L180) — **The per-round salvage probability bound** (the quantitative WHIR flip estimate): in any game that

### `queryCap` (5 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.queryCap` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsCoincidence.lean:148](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsCoincidence.lean#L148) — A mirror swap turns the answer-side capacity into the query-side capacity (for permutation entries;
- `def DuplexSpongeFS.Paper.queryCap` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean:76](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean#L76) — The query-side capacity segment (permutation entries only).
- `lemma DuplexSpongeFS.Paper.queryCap` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean:95](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean#L95) — (no docstring)
- `lemma DuplexSpongeFS.Paper.queryCap` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean:99](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean#L99) — (no docstring)
- `lemma DuplexSpongeFS.Paper.queryCap` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean:103](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/PaperBadEventsEngine.lean#L103) — (no docstring)

### `radical_cofactor_dvd_cofactor` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.radical_cofactor_dvd_cofactor` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:227](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L227) — **The overlap transfer (divisibility)**: any radical-split cofactor divides any fiber-split cofactor
- `theorem ArkLib.RadicalWire304.radical_cofactor_dvd_cofactor` [ArkLib/ToMathlib/RadicalAssembler.lean:246](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L246) — **The overlap transfer (divisibility)**: any radical-split cofactor divides any fiber-split cofactor

### `radical_fiber_ne_zero` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.radical_fiber_ne_zero` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:91](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L91) — The radical of the fiber is nonzero (unconditionally: `radical 0 = 1`).
- `theorem ArkLib.RadicalWire304.radical_fiber_ne_zero` [ArkLib/ToMathlib/RadicalAssembler.lean:110](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L110) — The radical of the fiber is nonzero (unconditionally: `radical 0 = 1`).

### `reduction_append_perfectCompleteness_msg` (2 declarations, 2 files)

- `theorem Reduction.reduction_append_perfectCompleteness_msg` [ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessMsg.lean:414](../../../ArkLib/OracleReduction/Composition/Sequential/AppendPerfectCompletenessMsg.lean#L414) — **Append perfect completeness, residual-free (message-seam case).** The public composition theorem w
- `def Reduction.reduction_append_perfectCompleteness_msg` [ArkLib/Whir113Keystone.lean:17](../../../ArkLib/Whir113Keystone.lean#L17) — Residual for append perfect-completeness in the message-first case. The previous theorem body ended

### `redundantEntryDSPaper_forward_inversion` (2 declarations, 2 files)

- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_forward_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:35](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L35) — Inversion of `redundantEntryDSPaper` at a forward slot: the certificate is an earlier entry with the
- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_forward_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:35](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L35) — Inversion of `redundantEntryDSPaper` at a forward slot: the certificate is an earlier entry with the

### `redundantEntryDSPaper_hash_inversion` (2 declarations, 2 files)

- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_hash_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L77) — Inversion of `redundantEntryDSPaper` at a hash slot: an earlier copy of the same hash entry (unchang
- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_hash_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L77) — Inversion of `redundantEntryDSPaper` at a hash slot: an earlier copy of the same hash entry (unchang

### `redundantEntryDSPaper_iff_sameClass` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.redundantEntryDSPaper_iff_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:267](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L267) — The paper redundancy predicate is exactly "an earlier class member exists".
- `lemma DuplexSpongeFS.EagerLazyDS.redundantEntryDSPaper_iff_sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:267](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L267) — The paper redundancy predicate is exactly "an earlier class member exists".

### `redundantEntryDSPaper_inverse_inversion` (2 declarations, 2 files)

- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_inverse_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:56](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L56) — Inversion of `redundantEntryDSPaper` at an inverse slot: the certificate is an earlier entry with th
- `lemma OracleSpec.QueryLog.redundantEntryDSPaper_inverse_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:56](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L56) — Inversion of `redundantEntryDSPaper` at an inverse slot: the certificate is an earlier entry with th

### `redundantEntryDS_forward_inversion` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.redundantEntryDS_forward_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:202](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L202) — Inversion of `redundantEntryDS` at a forward-permutation slot: the redundancy certificate is an earl
- `lemma DuplexSpongeFS.Sponge316.redundantEntryDS_forward_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:202](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L202) — Inversion of `redundantEntryDS` at a forward-permutation slot: the redundancy certificate is an earl

### `redundantEntryDS_hashEntry_inversion` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.redundantEntryDS_hashEntry_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:398](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L398) — Hash-slot inversion for the private `hashEntry` shorthand.
- `lemma DuplexSpongeFS.Sponge316.redundantEntryDS_hashEntry_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:398](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L398) — Hash-slot inversion for the private `hashEntry` shorthand.

### `redundantEntryDS_hash_inversion` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.redundantEntryDS_hash_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L248) — Inversion of `redundantEntryDS` at a hash slot: the redundancy certificate is an earlier copy of the
- `lemma DuplexSpongeFS.Sponge316.redundantEntryDS_hash_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L248) — Inversion of `redundantEntryDS` at a hash slot: the redundancy certificate is an earlier copy of the

### `redundantEntryDS_inv_inversion` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.redundantEntryDS_inv_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:825](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L825) — Inversion of `redundantEntryDS` at an inverse-permutation slot: the redundancy certificate is an ear
- `lemma DuplexSpongeFS.Sponge316.redundantEntryDS_inv_inversion` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:825](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L825) — Inversion of `redundantEntryDS` at an inverse-permutation slot: the redundancy certificate is an ear

### `redundantPaper_forward_capacity_prior` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.redundantPaper_forward_capacity_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:95](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L95) — A paper-redundant forward entry sharing a target capacity has an earlier **permutation** replacement
- `theorem OracleSpec.QueryLog.redundantPaper_forward_capacity_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:95](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L95) — A paper-redundant forward entry sharing a target capacity has an earlier **permutation** replacement

### `redundantPaper_inverse_capacity_prior` (2 declarations, 2 files)

- `theorem OracleSpec.QueryLog.redundantPaper_inverse_capacity_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L118) — A paper-redundant inverse entry sharing a target capacity has an earlier **permutation** replacement
- `theorem OracleSpec.QueryLog.redundantPaper_inverse_capacity_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L118) — A paper-redundant inverse entry sharing a target capacity has an earlier **permutation** replacement

### `redundant_forward_capacity_prior` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.redundant_forward_capacity_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:223](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L223) — A redundant forward entry that shares a target capacity has an earlier forward replacement that stil
- `theorem DuplexSpongeFS.Sponge316.redundant_forward_capacity_prior` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:223](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L223) — A redundant forward entry that shares a target capacity has an earlier forward replacement that stil

### `redundant_only_three` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.redundant_only_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:188](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L188) — No slot of `trc` other than `3` is redundant.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.redundant_only_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:188](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L188) — No slot of `trc` other than `3` is redundant.

### `redundant_three` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.redundant_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L184) — Entry 3 is in-tree-redundant: entry 2 is its same-direction swapped certificate.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.redundant_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L184) — Entry 3 is in-tree-redundant: entry 2 is its same-direction swapped certificate.

### `removeRedundantEntryDSPaper_pairwise_classDistinct` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_pairwise_classDistinct` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:627](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L627) — The dedup output is pairwise class-distinct.
- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_pairwise_classDistinct` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:627](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L627) — The dedup output is pairwise class-distinct.

### `removeRedundantEntryDSPaper_sublist` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:587](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L587) — The paper dedup output is a sublist of its input (each step erases one entry).
- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:587](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L587) — The paper dedup output is a sublist of its input (each step erases one entry).

### `removeRedundant_firstOcc` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundant_firstOcc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:975](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L975) — **Dedup positions are first occurrences.** There is an order embedding `f` of the dedup base trace i
- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundant_firstOcc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:975](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L975) — **Dedup positions are first occurrences.** There is an order embedding `f` of the dedup base trace i

### `removeRedundant_orderEmbedding` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundant_orderEmbedding` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:850](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L850) — The dedup base trace embeds into the raw log by a strictly monotone index map that preserves entries
- `theorem DuplexSpongeFS.EagerLazyDS.removeRedundant_orderEmbedding` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:850](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L850) — The dedup base trace embeds into the raw log by a strictly monotone index map that preserves entries

### `rootDecodedRadical` (2 declarations, 2 files)

- `def ArkLib.RadicalWire304.rootDecodedRadical` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:307](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L307) — **The radical decoded branch root** — `DecodedRootSupply.rootDecoded` with the GS split replaced by
- `def ArkLib.RadicalWire304.rootDecodedRadical` [ArkLib/ToMathlib/RadicalAssembler.lean:326](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L326) — **The radical decoded branch root** — `DecodedRootSupply.rootDecoded` with the GS split replaced by

### `rootDecodedRadical_val` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.rootDecodedRadical_val` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:319](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L319) — The radical decoded root's value, in general: `lc_H(z) · w(x₀, z)`.
- `theorem ArkLib.RadicalWire304.rootDecodedRadical_val` [ArkLib/ToMathlib/RadicalAssembler.lean:338](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L338) — The radical decoded root's value, in general: `lc_H(z) · w(x₀, z)`.

### `rootDecodedRadical_val_monic` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.rootDecodedRadical_val_monic` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:331](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L331) — The base-point fact at the radical decoded root (monic case): the value is exactly the surface's cen
- `theorem ArkLib.RadicalWire304.rootDecodedRadical_val_monic` [ArkLib/ToMathlib/RadicalAssembler.lean:350](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L350) — The base-point fact at the radical decoded root (monic case): the value is exactly the surface's cen

### `sameClass` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L248) — Class membership: equal or the swap.
- `def DuplexSpongeFS.EagerLazyDS.sameClass` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L248) — Class membership: equal or the swap.

### `sameClass_of_entryKeys` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.sameClass_of_entryKeys` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:520](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L520) — An entry whose inserted pair is `(a, b)` is class-equal to the forward entry `⟨inr (inl a), b⟩`: it
- `theorem DuplexSpongeFS.EagerLazyDS.sameClass_of_entryKeys` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:520](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L520) — An entry whose inserted pair is `(a, b)` is class-equal to the forward entry `⟨inr (inl a), b⟩`: it

### `sameClass_refl` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_refl` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:251](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L251) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_refl` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:251](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L251) — (no docstring)

### `sameClass_symm` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_symm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:253](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L253) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_symm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:253](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L253) — (no docstring)

### `sameClass_trans` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_trans` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:258](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L258) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.sameClass_trans` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:258](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L258) — (no docstring)

### `seqC` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TimePCounter.seqC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L87) — The backtrack chain `sB → sA → sB`, then `sa → sb`, ending at `sT`.
- `def DuplexSpongeFS.Sponge316.TimePCounter.seqC` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L87) — The backtrack chain `sB → sA → sB`, then `sa → sb`, ending at `sT`.

### `seqOne` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.seqOne` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:95](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L95) — Chain 1: the alternating loop `t1 → t2 → t1` on the first pair.
- `def DuplexSpongeFS.Sponge316.ForkCounter.seqOne` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:95](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L95) — Chain 1: the alternating loop `t1 → t2 → t1` on the first pair.

### `seqOne_ne_seqTwo` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.seqOne_ne_seqTwo` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:129](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L129) — The two chains are distinct (their `inputState` lists differ).
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.seqOne_ne_seqTwo` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:129](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L129) — The two chains are distinct (their `inputState` lists differ).

### `seqTwo` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.seqTwo` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:112](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L112) — Chain 2: the alternating loop `t3 → t4 → (cap t3 = cap t1)` on the second pair, ending at the same t
- `def DuplexSpongeFS.Sponge316.ForkCounter.seqTwo` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:112](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L112) — Chain 2: the alternating loop `t3 → t4 → (cap t3 = cap t1)` on the second pair, ending at the same t

### `slotList_length_le` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.slotList_length_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:160](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L160) — The slot list is at most twice the cache size.
- `lemma DuplexSpongeFS.EagerLazyDS.slotList_length_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:160](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L160) — The slot list is at most twice the cache size.

### `slots_pair_ASB` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_ASB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L114) — Entry 3 is the unique trace slot holding either orientation of the pair `(sA, sB)`.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_ASB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L114) — Entry 3 is the unique trace slot holding either orientation of the pair `(sA, sB)`.

### `slots_pair_asb` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_asb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L122) — Entry 1 is the unique trace slot holding either orientation of the pair `(sa, sb)`.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_asb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L122) — Entry 1 is the unique trace slot holding either orientation of the pair `(sa, sb)`.

### `split_branch_radical` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.split_branch_radical` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:148](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L148) — **The K4 split-and-branch package at the bundle, existential form** (`RadicalBranch.exists_radical_s
- `theorem ArkLib.RadicalWire304.split_branch_radical` [ArkLib/ToMathlib/RadicalAssembler.lean:167](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L167) — **The K4 split-and-branch package at the bundle, existential form** (`RadicalBranch.exists_radical_s

### `split_canonical_radical` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.split_canonical_radical` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:118](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L118) — **K4 split (the canonical radical split)**: at the bundle's own monic `H`, the RADICAL of the fiber
- `theorem ArkLib.RadicalWire304.split_canonical_radical` [ArkLib/ToMathlib/RadicalAssembler.lean:137](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L137) — **K4 split (the canonical radical split)**: at the bundle's own monic `H`, the RADICAL of the fiber

### `step3` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step3` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:672](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L672) — Seam 2 (`firstChallenge ▷ …`, message seam: the right block opens with the first sum-check's leading
- `theorem Spartan.Spec.Bricks.step3` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:235](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L235) — Seam 2 (`firstChallenge ▷ …`, message seam: the right block opens with the first sum-check's leading

### `step4` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step4` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:634](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L634) — Seam 3 (`firstSumcheck ▷ …`, message seam: the right block opens with the bundled eval-claim `P_to_V
- `theorem Spartan.Spec.Bricks.step4` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:197](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L197) — Seam 3 (`firstSumcheck ▷ …`, message seam: the right block opens with the bundled eval-claim `P_to_V

### `step5` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step5` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:612](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L612) — Seam 4 (`sendEvalClaim ▷ …`, **challenge** seam: the right block opens with the linear-combination `
- `theorem Spartan.Spec.Bricks.step5` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:175](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L175) — Seam 4 (`sendEvalClaim ▷ …`, **challenge** seam: the right block opens with the linear-combination `

### `step6` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step6` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:571](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L571) — Seam 5 (`linearCombination ▷ …`, message seam: the right block opens with the second sum-check's lea
- `theorem Spartan.Spec.Bricks.step6` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:134](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L134) — Seam 5 (`linearCombination ▷ …`, message seam: the right block opens with the second sum-check's lea

### `step7` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step7` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:542](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L542) — Seam 6 (`prependRLCTarget ▷ …`, message seam through the 0-round left adapter).
- `theorem Spartan.Spec.Bricks.step7` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:105](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L105) — Seam 6 (`prependRLCTarget ▷ …`, message seam through the 0-round left adapter).

### `step8` (2 declarations, 2 files)

- `theorem Spartan.Spec.Bricks.step8` [ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean:517](../../../ArkLib/ProofSystem/Spartan/ComposedCompleteness.lean#L517) — Seam 7 (`secondSumcheck ▷ finalCheck`, empty trailing seam).
- `theorem Spartan.Spec.Bricks.step8` [ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean:80](../../../ArkLib/ProofSystem/Spartan/TightComposedCompleteness.lean#L80) — Seam 7 (`secondSumcheck ▷ finalCheck`, empty trailing seam).

### `stepCache` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.stepCache` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:51](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L51) — Fold one log entry onto a cache: first occurrence caches, repeats change nothing.
- `def DuplexSpongeFS.EagerLazyDS.stepCache` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:51](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L51) — Fold one log entry onto a cache: first occurrence caches, repeats change nothing.

### `stepCache_caches_fresh_hash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:113](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L113) — A fresh hash entry creates its record.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:113](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L113) — A fresh hash entry creates its record.

### `stepCache_caches_fresh_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:123](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L123) — A fresh forward permutation entry creates its pair.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:123](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L123) — A fresh forward permutation entry creates its pair.

### `stepCache_caches_fresh_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:134](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L134) — A fresh inverse permutation entry creates its (answer, query) pair.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_caches_fresh_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:134](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L134) — A fresh inverse permutation entry creates its (answer, query) pair.

### `stepCache_fwdNodup` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_fwdNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:678](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L678) — One non-anchored fold step preserves forward-key distinctness.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_fwdNodup` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:678](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L678) — One non-anchored fold step preserves forward-key distinctness.

### `stepCache_hash_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:315](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L315) — The hash cache only grows: an already-cached answer survives one fold step.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:315](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L315) — The hash cache only grows: an already-cached answer survives one fold step.

### `stepCache_hash_mono'` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_mono'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L53) — A cached hash record survives one fold step.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_mono'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L53) — A cached hash record survives one fold step.

### `stepCache_hash_provenance` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1187](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1187) — **Hash-cache provenance (one step).** A hash answer present after a step was already cached or was i
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_hash_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1187](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1187) — **Hash-cache provenance (one step).** A hash answer present after a step was already cached or was i

### `stepCache_noop_hash` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:173](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L173) — A hash entry whose key is cached is a `stepCache` no-op.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_hash` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:173](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L173) — A hash entry whose key is cached is a `stepCache` no-op.

### `stepCache_noop_of_classRedAt_consistent` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_of_classRedAt_consistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:419](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L419) — In a consistent log, a class-redundant slot is a `stepCache` no-op at its prefix fold. This is the c
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_of_classRedAt_consistent` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:419](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L419) — In a consistent log, a class-redundant slot is a `stepCache` no-op at its prefix fold. This is the c

### `stepCache_noop_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L184) — A forward entry whose key is cached is a `stepCache` no-op.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:184](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L184) — A forward entry whose key is cached is a `stepCache` no-op.

### `stepCache_noop_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:198](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L198) — An inverse entry whose key is cached is a `stepCache` no-op.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_noop_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:198](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L198) — An inverse entry whose key is cached is a `stepCache` no-op.

### `stepCache_pair_mono` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_pair_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/CacheProvenance.lean#L77) — A cached permutation pair survives one fold step.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_pair_mono` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58CacheProvenance.lean#L77) — A cached permutation pair survives one fold step.

### `stepCache_pair_provenance` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_pair_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:716](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L716) — **Pair provenance (one step)**: a pair in the cache after a step was already there or was inserted b
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_pair_provenance` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:716](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L716) — **Pair provenance (one step)**: a pair in the cache after a step was already there or was inserted b

### `stepCache_perm_sublist` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_perm_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L300) — The permutation cache only grows (as a sublist) along one fold step.
- `theorem DuplexSpongeFS.EagerLazyDS.stepCache_perm_sublist` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L300) — The permutation cache only grows (as a sublist) along one fold step.

### `step_determinism` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Paper.step_determinism` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:76](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L76) — **U1 (step determinism, paper event)** — CO25 Claim 5.19, Eq. 44 step: off `EPaper`, two chain steps
- `theorem DuplexSpongeFS.Paper.step_determinism` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:76](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L76) — **U1 (step determinism, paper event)** — CO25 Claim 5.19, Eq. 44 step: off `EPaper`, two chain steps

### `step_determinism_paper` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.Sponge316.step_determinism_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L300) — **Step determinism, paper event**: off `BadEventDSPaper.E`, two family chain steps whose output capa
- `theorem DuplexSpongeFS.Sponge316.step_determinism_paper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:300](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L300) — **Step determinism, paper event**: off `BadEventDSPaper.E`, two family chain steps whose output capa

### `stirInitReduction_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem StirIOP.Round3.stirInitReduction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Stir/InitAppendRbr.lean:123](../../../ArkLib/ProofSystem/Stir/InitAppendRbr.lean#L123) — RBR knowledge soundness of the initial block, phrased on `stirInitReduction`'s verifier.
- `theorem StirIOP.Round3.stirInitReduction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Stir/InitRbrSoundness.lean:109](../../../ArkLib/ProofSystem/Stir/InitRbrSoundness.lean#L109) — RBR knowledge soundness of the initial block, phrased on `stirInitReduction`'s verifier.

### `stirInitVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem StirIOP.Round3.stirInitVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Stir/InitAppendRbr.lean:84](../../../ArkLib/ProofSystem/Stir/InitAppendRbr.lean#L84) — **RBR knowledge soundness of the initial `[C_fold]` block, with zero error.** The verifier is a pure
- `theorem StirIOP.Round3.stirInitVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Stir/InitRbrSoundness.lean:70](../../../ArkLib/ProofSystem/Stir/InitRbrSoundness.lean#L70) — **RBR knowledge soundness of the initial `[C_fold]` block, with zero error.** The verifier is a pure

### `stirInitVerifier_toVerifier_eq` (2 declarations, 2 files)

- `theorem StirIOP.Round3.stirInitVerifier_toVerifier_eq` [ArkLib/ProofSystem/Stir/InitAppendRbr.lean:71](../../../ArkLib/ProofSystem/Stir/InitAppendRbr.lean#L71) — The initial block's relay verifier, seen as a non-oracle verifier, is the *pure* deterministic verif
- `theorem StirIOP.Round3.stirInitVerifier_toVerifier_eq` [ArkLib/ProofSystem/Stir/InitRbrSoundness.lean:57](../../../ArkLib/ProofSystem/Stir/InitRbrSoundness.lean#L57) — The initial block's relay verifier, seen as a non-oracle verifier, is the *pure* deterministic verif

### `stirInitVerifier_toVerifier_run` (2 declarations, 2 files)

- `theorem StirIOP.Round3.stirInitVerifier_toVerifier_run` [ArkLib/ProofSystem/Stir/InitAppendRbr.lean:58](../../../ArkLib/ProofSystem/Stir/InitAppendRbr.lean#L58) — Running the initial block's (oracle) verifier deterministically returns the fold challenge together
- `theorem StirIOP.Round3.stirInitVerifier_toVerifier_run` [ArkLib/ProofSystem/Stir/InitRbrSoundness.lean:44](../../../ArkLib/ProofSystem/Stir/InitRbrSoundness.lean#L44) — Running the initial block's (oracle) verifier deterministically returns the fold challenge together

### `stirInitVerify` (2 declarations, 2 files)

- `def StirIOP.Round3.stirInitVerify` [ArkLib/ProofSystem/Stir/InitAppendRbr.lean:51](../../../ArkLib/ProofSystem/Stir/InitAppendRbr.lean#L51) — The deterministic statement map computed by the initial block's relay verifier: read the fold challe
- `def StirIOP.Round3.stirInitVerify` [ArkLib/ProofSystem/Stir/InitRbrSoundness.lean:37](../../../ArkLib/ProofSystem/Stir/InitRbrSoundness.lean#L37) — The deterministic statement map computed by the initial block's relay verifier: read the fold challe

### `sudan_list_bound` (2 declarations, 2 files)

- `theorem R15.sudan_list_bound` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:335](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L335) — **End-to-end Sudan (multiplicity-1) list bound.**  Let `F` be a field, `α : Fin n → F` injective eva
- `theorem R15.sudan_list_bound` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:335](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L335) — **End-to-end Sudan (multiplicity-1) list bound.**  Let `F` be a field, `α : Fin n → F` injective eva

### `sudan_list_bound_ZMod13` (2 declarations, 2 files)

- `theorem R15.sudan_list_bound_ZMod13` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:402](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L402) — **Concrete Sudan instance.** Over `ZMod 13` with the 12 evaluation points `0,…,11`: any list of poly
- `theorem R15.sudan_list_bound_ZMod13` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:402](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L402) — **Concrete Sudan instance.** Over `ZMod 13` with the 12 evaluation points `0,…,11`: any list of poly

### `sudan_list_bound_filter` (2 declarations, 2 files)

- `theorem R15.sudan_list_bound_filter` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:371](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L371) — Filter form (when `F` has decidable equality): the agreement hypothesis stated as a cardinality of `
- `theorem R15.sudan_list_bound_filter` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:371](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L371) — Filter form (when `F` has decidable equality): the agreement hypothesis stated as a cardinality of `

### `sum_lemma58StepBound_le` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.sum_lemma58StepBound_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:489](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L489) — The Gauss-sum domination: below half the state space, the accumulated step bounds sum to at most `2T
- `theorem DuplexSpongeFS.EagerLazyDS.sum_lemma58StepBound_le` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:489](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L489) — The Gauss-sum domination: below half the state space, the accumulated step bounds sum to at most `2T

### `sum_map_two_mul_sub_one` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.sum_map_two_mul_sub_one` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2KeystoneReindex.lean:183](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/P2KeystoneReindex.lean#L183) — Auxiliary: `∑_{l ∈ λ} (2 l - 1) = 2 c - (number of parts)` (truncated ℕ subtraction). The per-part s
- `theorem BCIKS20.HenselNumerator.sum_map_two_mul_sub_one` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/RestrictedFaaDiBrunoXiTelescope.lean:94](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/RestrictedFaaDiBrunoXiTelescope.lean#L94) — **The LHS `ξ`-denominator exponent of a partition (axiom-clean).** The assembled-series coefficient

### `sum_range_two_mul_add_one` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.sum_range_two_mul_add_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean:481](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Flag.lean#L481) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.sum_range_two_mul_add_one` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean:481](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Flag.lean#L481) — (no docstring)

### `support_flagged_logged` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.support_flagged_logged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:177](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L177) — **The master run correspondence**: every support element of the flagged run of the logged program ha
- `theorem DuplexSpongeFS.EagerLazyDS.support_flagged_logged` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:177](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L177) — **The master run correspondence**: every support element of the flagged run of the logged program ha

### `support_oracleReduction_run` (2 declarations, 2 files)

- `theorem CheckClaim.support_oracleReduction_run` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:186](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L186) — **The pred-generic support collapse for the full honest `CheckClaim` oracle reduction**: the run onl
- `theorem CheckClaim.support_oracleReduction_run` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:169](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L169) — **The pred-generic support collapse for the full honest `CheckClaim` oracle reduction**: the run onl

### `support_simulateQ_subset'` (2 declarations, 2 files)

- `lemma CheckClaim.support_simulateQ_subset'` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:64](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L64) — Outputs of a simulated computation (into another `OracleComp`) are outputs of the original computati
- `lemma CheckClaim.support_simulateQ_subset'` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:72](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L72) — Outputs of a simulated computation (into another `OracleComp`) are outputs of the original computati

### `support_toVerifier_run` (2 declarations, 2 files)

- `theorem CheckClaim.support_toVerifier_run` [ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean:160](../../../ArkLib/ProofSystem/Spartan/FinalCheckTightComplete.lean#L160) — **The pred-generic support collapse for the compiled `CheckClaim` oracle verifier**: the run only ev
- `theorem CheckClaim.support_toVerifier_run` [ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean:143](../../../ArkLib/ProofSystem/Spartan/TightFinalCompleteness.lean#L143) — **The pred-generic support collapse for the compiled `CheckClaim` oracle verifier**: the run only ev

### `swapEntry` (2 declarations, 2 files)

- `def DuplexSpongeFS.EagerLazyDS.swapEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:237](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L237) — The opposite-direction form of an entry (hash entries are self-paired).
- `def DuplexSpongeFS.EagerLazyDS.swapEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:237](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L237) — The opposite-direction form of an entry (hash entries are self-paired).

### `swapEntry_eq_mirrorOf` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.swapEntry_eq_mirrorOf` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Extraction.lean#L46) — The Correspondence-file `swapEntry` and the Engine-file `mirrorOf` are the same map.
- `theorem DuplexSpongeFS.EagerLazyDS.swapEntry_eq_mirrorOf` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean:46](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Extraction.lean#L46) — The Correspondence-file `swapEntry` and the Engine-file `mirrorOf` are the same map.

### `swapEntry_swapEntry` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.swapEntry_swapEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:242](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L242) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.swapEntry_swapEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:242](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L242) — (no docstring)

### `swapKey_cached_after_consistent_perm` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.swapKey_cached_after_consistent_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L248) — After a consistent forward step, the **inverse** key is cached: fresh creates `(a, b)` (serving the
- `theorem DuplexSpongeFS.EagerLazyDS.swapKey_cached_after_consistent_perm` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:248](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L248) — After a consistent forward step, the **inverse** key is cached: fresh creates `(a, b)` (serving the

### `swapKey_cached_after_consistent_permInv` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.swapKey_cached_after_consistent_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:266](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L266) — After a consistent inverse step, the **forward** key is cached: fresh creates `(a, b)` (serving the
- `theorem DuplexSpongeFS.EagerLazyDS.swapKey_cached_after_consistent_permInv` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:266](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L266) — After a consistent inverse step, the **forward** key is cached: fresh creates `(a, b)` (serving the

### `take_inner_split` (2 declarations, 2 files)

- `theorem DuplexSpongeFS.EagerLazyDS.take_inner_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean:1314](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Correspondence.lean#L1314) — The inner split of `take (f j)` at an earlier position `f j'`.
- `theorem DuplexSpongeFS.EagerLazyDS.take_inner_split` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean:1314](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Correspondence.lean#L1314) — The inner split of `take (f j)` at an earlier position `f j'`.

### `take_split_getElem` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.EagerLazyDS.take_split_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean:399](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Freshness.lean#L399) — (no docstring)
- `lemma DuplexSpongeFS.EagerLazyDS.take_split_getElem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean:399](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma58Freshness.lean#L399) — (no docstring)

### `threshold_lt_pow_div` (2 declarations, 2 files)

- `theorem CodingTheory.threshold_lt_pow_div` [ArkLib/Data/CodingTheory/ProximityGap/ListDecodingCapacityOverflow.lean:40](../../../ArkLib/Data/CodingTheory/ProximityGap/ListDecodingCapacityOverflow.lean#L40) — **`rpow` overflow bridge.** For `q > 1`, `0 < n1`, `0 < εq`, if `logb q (n1·εq) < E` then `εq < q^E
- `theorem CodingTheory.threshold_lt_pow_div` [ArkLib/Data/CodingTheory/ProximityGap/UpToCapacityListDecodingFalse.lean:45](../../../ArkLib/Data/CodingTheory/ProximityGap/UpToCapacityListDecodingFalse.lean#L45) — **`rpow` overflow bridge.** For `q > 1`, `0 < n1`, `0 < εq`, `logb q (n1·εq) < E → εq < q^E/n1`.

### `totalDegree_ehQ_le` (2 declarations, 2 files)

- `lemma MvPolynomial.totalDegree_ehQ_le` [ArkLib/ToMathlib/RestrictedSumset.lean:265](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L265) — `ehQ Cset` has total degree at most `\|Cset\| + 1`.
- `lemma MvPolynomial.totalDegree_ehQ_le` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:316](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L316) — `ehQ h Cset` has total degree at most `deg(vdmX) + \|Cset\|`.

### `totalDegree_prod_sub_pow_le` (2 declarations, 2 files)

- `lemma MvPolynomial.totalDegree_prod_sub_pow_le` [ArkLib/ToMathlib/RestrictedSumset.lean:183](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L183) — **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{\|s\|}` by a pol
- `lemma MvPolynomial.totalDegree_prod_sub_pow_le` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:195](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L195) — **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{\|s\|}` by a pol

### `trc` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TimePCounter.trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:81](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L81) — The raw countermodel trace.
- `def DuplexSpongeFS.Sponge316.TimePCounter.trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:81](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L81) — The raw countermodel trace.

### `trc'` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.TimePCounter.trc'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L84) — The dedup'd trace: entry 3 (`(p, sA, sB)`) is in-tree-redundant w.r.t. entry 2.
- `def DuplexSpongeFS.Sponge316.TimePCounter.trc'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L84) — The dedup'd trace: entry 3 (`(p, sA, sB)`) is in-tree-redundant w.r.t. entry 2.

### `trc'_noRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.TimePCounter.trc'_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:218](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L218) — No slot of the 3-entry trace `trc'` is redundant.
- `lemma DuplexSpongeFS.Sponge316.TimePCounter.trc'_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:218](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L218) — No slot of the 3-entry trace `trc'` is redundant.

### `trcA` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.trcA` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L84) — Intermediate trace after erasing slot 2 first.
- `def DuplexSpongeFS.Sponge316.ForkCounter.trcA` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L84) — Intermediate trace after erasing slot 2 first.

### `trcA_redundant_only` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcA_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:218](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L218) — In `trcA`, only slot 3 is redundant.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcA_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:218](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L218) — In `trcA`, only slot 3 is redundant.

### `trcA_redundant_three` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcA_redundant_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:214](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L214) — In `trcA = [eH, q1, q3, q4]`, slot 3 is redundant (slot 2 is its certificate).
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcA_redundant_three` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:214](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L214) — In `trcA = [eH, q1, q3, q4]`, slot 3 is redundant (slot 2 is its certificate).

### `trcB` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.trcB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L87) — Intermediate trace after erasing slot 4 first.
- `def DuplexSpongeFS.Sponge316.ForkCounter.trcB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L87) — Intermediate trace after erasing slot 4 first.

### `trcB_redundant_only` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcB_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:249](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L249) — In `trcB`, only slot 2 is redundant.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcB_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:249](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L249) — In `trcB`, only slot 2 is redundant.

### `trcB_redundant_two` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcB_redundant_two` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:245](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L245) — In `trcB = [eH, q1, q2, q3]`, slot 2 is redundant (slot 1 is its certificate).
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcB_redundant_two` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:245](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L245) — In `trcB = [eH, q1, q2, q3]`, slot 2 is redundant (slot 1 is its certificate).

### `trcD` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.trcD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L90) — The dedup fixpoint: both erasure orders converge here.
- `def DuplexSpongeFS.Sponge316.ForkCounter.trcD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:90](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L90) — The dedup fixpoint: both erasure orders converge here.

### `trcD_noRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcD_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:280](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L280) — No slot of the 3-entry trace `trcD` is redundant.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcD_noRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:280](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L280) — No slot of the 3-entry trace `trcD` is redundant.

### `trcF` (2 declarations, 2 files)

- `def DuplexSpongeFS.Sponge316.ForkCounter.trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:81](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L81) — The raw countermodel trace.
- `def DuplexSpongeFS.Sponge316.ForkCounter.trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:81](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L81) — The raw countermodel trace.

### `trcF_redundant_four` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_four` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:175](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L175) — Slot 4 (`(p, t4, t3)`) is in-tree-redundant: slot 3 is its swapped certificate.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_four` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:175](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L175) — Slot 4 (`(p, t4, t3)`) is in-tree-redundant: slot 3 is its swapped certificate.

### `trcF_redundant_only` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:179](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L179) — No slot of `trcF` other than `2` and `4` is redundant.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_only` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:179](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L179) — No slot of `trcF` other than `2` and `4` is redundant.

### `trcF_redundant_two` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_two` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:171](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L171) — Slot 2 (`(p, t2, t1)`) is in-tree-redundant: slot 1 is its swapped certificate.
- `lemma DuplexSpongeFS.Sponge316.ForkCounter.trcF_redundant_two` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:171](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L171) — Slot 2 (`(p, t2, t1)`) is in-tree-redundant: slot 1 is its swapped certificate.

### `twoSurvivors_eraseIdx` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.twoSurvivors_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:170](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L170) — One-step preservation: erasing a paper-redundant entry preserves the two-survivor shape (the guarded
- `lemma DuplexSpongeFS.Sponge316.twoSurvivors_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:170](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L170) — One-step preservation: erasing a paper-redundant entry preserves the two-survivor shape (the guarded

### `twoSurvivors_removeRedundant` (2 declarations, 2 files)

- `lemma DuplexSpongeFS.Sponge316.twoSurvivors_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:194](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L194) — **Two-survivor dedup transport**: both guarded slots survive paper dedup, in order.
- `lemma DuplexSpongeFS.Sponge316.twoSurvivors_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:194](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L194) — **Two-survivor dedup transport**: both guarded slots survive paper dedup, in order.

### `two_element_list_witness` (2 declarations, 2 files)

- `theorem R15.two_element_list_witness` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:425](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L425) — **Non-vacuity / genuine list regime.**  For the explicit received word `wWit` over `ZMod 13`, the ex
- `theorem R15.two_element_list_witness` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:425](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L425) — **Non-vacuity / genuine list regime.**  For the explicit received word `wWit` over `ZMod 13`, the ex

### `wWit` (2 declarations, 2 files)

- `def R15.wWit` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:418](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L418) — Explicit received word: agrees with `X` on indices `0,…,5` and with `0` on `6,…,11` (and on `0`).
- `def R15.wWit` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:418](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L418) — Explicit received word: agrees with `X` on indices `0,…,5` and with `0` on `6,…,11` (and on `0`).

### `w_in_C` (2 declarations, 2 files)

- `lemma w_in_C` [ArkLib/Data/CodingTheory/ProximityGap/PromotedHypothesesB.lean:56](../../../ArkLib/Data/CodingTheory/ProximityGap/PromotedHypothesesB.lean#L56) — (no docstring)
- `lemma w_in_C` [ArkLib/Data/CodingTheory/Quarantine/HypothesesRefutations.lean:35](../../../ArkLib/Data/CodingTheory/Quarantine/HypothesesRefutations.lean#L35) — (no docstring)

### `weight` (2 declarations, 2 files)

- `def weight` [ArkLib/Data/CodingTheory/ProximityGap/PromotedHypothesesB.lean:62](../../../ArkLib/Data/CodingTheory/ProximityGap/PromotedHypothesesB.lean#L62) — (no docstring)
- `def weight` [ArkLib/Data/CodingTheory/Quarantine/Hypotheses.lean:19](../../../ArkLib/Data/CodingTheory/Quarantine/Hypotheses.lean#L19) — (no docstring)

### `xiCert_eq_derivativeCert` (2 declarations, 2 files)

- `theorem ArkLib.XiCertReduction.xiCert_eq_derivativeCert` [ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean:127](../../../ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean#L127) — **The value identity (monic)**: the `ξ`-certificate equals the derivative reading along the surface,
- `theorem ArkLib.XiCertReduction.xiCert_eq_derivativeCert` [ArkLib/ToMathlib/XiCertReduction.lean:158](../../../ArkLib/ToMathlib/XiCertReduction.lean#L158) — **The value identity (monic)**: the `ξ`-certificate equals the derivative reading along the surface,

### `xiCert_eq_derivativeCert_of_centreFold_root` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.xiCert_eq_derivativeCert_of_centreFold_root` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:366](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L366) — **The `ξ`-certificate value identity from the centre-fold root directly** — mirror of `XiCertReducti
- `theorem ArkLib.RadicalWire304.xiCert_eq_derivativeCert_of_centreFold_root` [ArkLib/ToMathlib/RadicalAssembler.lean:385](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L385) — **The `ξ`-certificate value identity from the centre-fold root directly** — mirror of `XiCertReducti

### `xiCert_eval_monic_radical` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.xiCert_eval_monic_radical` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:402](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L402) — **The `ξ`-certificate reading at the radical decoded root** (monic case) — mirror of `BranchCertific
- `theorem ArkLib.RadicalWire304.xiCert_eval_monic_radical` [ArkLib/ToMathlib/RadicalAssembler.lean:421](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L421) — **The `ξ`-certificate reading at the radical decoded root** (monic case) — mirror of `BranchCertific

### `xiCert_isUnit` (2 declarations, 2 files)

- `theorem ArkLib.XiCertReduction.xiCert_isUnit` [ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean:156](../../../ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean#L156) — **The `ξ`-certificate is a UNIT** (monic): the structural GS facts force the certificate to be a non
- `theorem ArkLib.XiCertReduction.xiCert_isUnit` [ArkLib/ToMathlib/XiCertReduction.lean:187](../../../ArkLib/ToMathlib/XiCertReduction.lean#L187) — **The `ξ`-certificate is a UNIT** (monic): the structural GS facts force the certificate to be a non

### `xiCert_isUnit_of_centreFold_root` (2 declarations, 2 files)

- `theorem ArkLib.RadicalWire304.xiCert_isUnit_of_centreFold_root` [ArkLib/ToMathlib/MinimalSurfaceChain.lean:392](../../../ArkLib/ToMathlib/MinimalSurfaceChain.lean#L392) — **The `ξ`-certificate is a UNIT from the centre-fold root** — mirror of `XiCertReduction.xiCert_isUn
- `theorem ArkLib.RadicalWire304.xiCert_isUnit_of_centreFold_root` [ArkLib/ToMathlib/RadicalAssembler.lean:411](../../../ArkLib/ToMathlib/RadicalAssembler.lean#L411) — **The `ξ`-certificate is a UNIT from the centre-fold root** — mirror of `XiCertReduction.xiCert_isUn

### `xiCert_natDegree_eq_zero` (2 declarations, 2 files)

- `theorem ArkLib.XiCertReduction.xiCert_natDegree_eq_zero` [ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean:178](../../../ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean#L178) — The `ξ`-certificate has degree zero: it contributes nothing to the `hbig` budget.
- `theorem ArkLib.XiCertReduction.xiCert_natDegree_eq_zero` [ArkLib/ToMathlib/XiCertReduction.lean:209](../../../ArkLib/ToMathlib/XiCertReduction.lean#L209) — The `ξ`-certificate has degree zero: it contributes nothing to the `hbig` budget.

### `xiCert_ne_zero` (2 declarations, 2 files)

- `theorem ArkLib.XiCertReduction.xiCert_ne_zero` [ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean:169](../../../ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean#L169) — **THE CLOSURE: `hxi` holds.**  The `ξ`-certificate nonvanishing of `BranchCertificates.gammaGenuine_
- `theorem ArkLib.XiCertReduction.xiCert_ne_zero` [ArkLib/ToMathlib/XiCertReduction.lean:200](../../../ArkLib/ToMathlib/XiCertReduction.lean#L200) — **THE CLOSURE: `hxi` holds.**  The `ξ`-certificate nonvanishing of `BranchCertificates.gammaGenuine_

### `xi_ne_zero` (2 declarations, 2 files)

- `theorem ArkLib.XiCertReduction.xi_ne_zero` [ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean:188](../../../ArkLib/ToMathlib/BCIKS20GlobalAssembler.lean#L188) — **`ξ ≠ 0` holds unconditionally** (from `embeddingOf𝒪Into𝕃_ξ_ne_zero`): the `hξ` hypothesis of the t
- `theorem ArkLib.XiCertReduction.xi_ne_zero` [ArkLib/ToMathlib/XiCertReduction.lean:219](../../../ArkLib/ToMathlib/XiCertReduction.lean#L219) — **`ξ ≠ 0` holds unconditionally** (from `embeddingOf𝒪Into𝕃_ξ_ne_zero`): the `hξ` hypothesis of the t

## Near-duplicate docstrings (Jaccard ≥ 0.85, 240 cross-file pairs)

Each pair has docstrings sharing a high fraction of (4+-letter) words, in different files. Most are unrelated coincidences in boilerplate; look for pairs where the *concept* matches.

- **1.00** `ArkLib.CS25.code_covered_count_johnson_radius_entropy` [ArkLib/Data/CodingTheory/ProximityGap/CS25CodeCoveredFractionJohnsonEntropy.lean:66](../../../ArkLib/Data/CodingTheory/ProximityGap/CS25CodeCoveredFractionJohnsonEntropy.lean#L66) vs `ArkLib.CS25.rs_covered_count_johnson_radius_entropy` [ArkLib/Data/CodingTheory/ProximityGap/CS25RSCoveredFractionJohnsonEntropy.lean:66](../../../ArkLib/Data/CodingTheory/ProximityGap/CS25RSCoveredFractionJohnsonEntropy.lean#L66)
    - a: **Existential entropy-form covered fraction up to the Johnson radius (#232).**  The qualitative John
    - b: **Existential entropy-form RS covered fraction up to the Johnson radius (#232).** The qualitative RS
- **1.00** `ArkLib.CS25.code_covered_count_johnson_radius_sqrt_entropy` [ArkLib/Data/CodingTheory/ProximityGap/CS25CodeCoveredFractionJohnsonEntropy.lean:89](../../../ArkLib/Data/CodingTheory/ProximityGap/CS25CodeCoveredFractionJohnsonEntropy.lean#L89) vs `ArkLib.CS25.rs_covered_count_johnson_radius_sqrt_entropy` [ArkLib/Data/CodingTheory/ProximityGap/CS25RSCoveredFractionJohnsonEntropy.lean:91](../../../ArkLib/Data/CodingTheory/ProximityGap/CS25RSCoveredFractionJohnsonEntropy.lean#L91)
    - a: **Entropy covered fraction from the explicit sqrt-form Johnson radius (#232).**  The textbook `√(T·B
    - b: **Entropy RS covered fraction from the explicit sqrt-form Johnson radius (#232).**  The textbook `√(
- **1.00** `ArkLib.ClosedBoundaryFaithfulFloorCellWitness.rate_eq_half` [ArkLib/ToMathlib/ClosedBoundaryFaithfulFloorCell.lean:351](../../../ArkLib/ToMathlib/ClosedBoundaryFaithfulFloorCell.lean#L351) vs `ArkLib.RemainingCoreWitness.rate_eq_half` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/RemainingCore.lean:190](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/RemainingCore.lean#L190)
    - a: The witness Reed–Solomon code has rate exactly `1/2` (`dim 2`, length `4`).
    - b: The witness Reed–Solomon code has rate exactly `1/2` (`dim 2`, length `4`).
- **1.00** `ArkLib.CodingTheory.CapacityLowerSharpen.agreeCount` [ArkLib/Data/CodingTheory/ProximityGap/ListCapacityFieldIndependent.lean:185](../../../ArkLib/Data/CodingTheory/ProximityGap/ListCapacityFieldIndependent.lean#L185) vs `ArkLib.CodingTheory.Round4InteriorList.agreeCount` [ArkLib/Data/CodingTheory/ProximityGap/InteriorListCountBridge.lean:199](../../../ArkLib/Data/CodingTheory/ProximityGap/InteriorListCountBridge.lean#L199)
    - a: The agreement count (number of coordinates where two words coincide).
    - b: The agreement count (number of coordinates where two words coincide).
- **1.00** `ArkLib.CodingTheory.CapacityLowerSharpen.pS_eval_eq_on_S` [ArkLib/Data/CodingTheory/ProximityGap/ListCapacityFieldIndependent.lean:82](../../../ArkLib/Data/CodingTheory/ProximityGap/ListCapacityFieldIndependent.lean#L82) vs `ArkLib.CodingTheory.Round4InteriorList.pSt_eval_eq_on_S` [ArkLib/Data/CodingTheory/ProximityGap/InteriorListCountBridge.lean:89](../../../ArkLib/Data/CodingTheory/ProximityGap/InteriorListCountBridge.lean#L89)
    - a: `p_S` agrees with `g` (the received word) on every coordinate of `S`: the product vanishes on `S`, s
    - b: `p_S` agrees with `g` (the received word) on every coordinate of `S`: the product vanishes on `S`, s
- **1.00** `ArkLib.CodingTheory.CapacityLowerSharpen.prod_X_sub_C_injOn_subsets` [ArkLib/Data/CodingTheory/ProximityGap/ListCapacityFieldIndependent.lean:128](../../../ArkLib/Data/CodingTheory/ProximityGap/ListCapacityFieldIndependent.lean#L128) vs `ArkLib.CodingTheory.Round4InteriorList.prod_X_sub_C_injOn_subsets` [ArkLib/Data/CodingTheory/ProximityGap/InteriorListCountBridge.lean:128](../../../ArkLib/Data/CodingTheory/ProximityGap/InteriorListCountBridge.lean#L128)
    - a: The two root products are equal as polynomials iff the subsets are equal (`D` injective).
    - b: The two root products are equal as polynomials iff the subsets are equal (`D` injective).
- **1.00** `ArkLib.CodingTheory.TinyInteriorF11.DD` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11.lean:61](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11.lean#L61) vs `ArkLib.CodingTheory.TinyInteriorK3.D` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:84](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L84)
    - a: The evaluation domain: all eleven points of `F₁₁`, indexed by `Fin 11` via `DD i = i`.
    - b: The evaluation domain: all eleven points of `F₁₁`, indexed by `Fin 11` via `D i = i`.
- **1.00** `ArkLib.CodingTheory.TinyInteriorK3.fact_prime_eleven` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:81](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L81) vs `ArkLib.CodingTheory.TinyInteriorPin.fact_prime_seven` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:65](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L65)
    - a: `11` is prime, so `ZMod 11` is a field. This is what makes `RS[F₁₁, F₁₁, 3]` a genuine Reed–Solomon
    - b: `7` is prime, so `ZMod 7` is a field. This is what makes `RS[F₇, F₇, 2]` a genuine Reed–Solomon code
- **1.00** `ArkLib.CodingTheory.TinyInteriorK3.six_elevenths_strictly_interior` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean:256](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorPinF11K3.lean#L256) vs `ArkLib.CodingTheory.TinyInteriorPin.four_sevenths_strictly_interior` [ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean:215](../../../ArkLib/Data/CodingTheory/ProximityGap/ListInteriorDataPointF7.lean#L215)
    - a: **Gap placement.** The relative radius `δ = 6/11` (agreement `a = 5` out of `n = 11`) is strictly be
    - b: **Gap placement.** The relative radius `δ = 4/7` (agreement `a = 3` out of `n = 7`) is strictly betw
- **1.00** `ArkLib.FactorKill.eval_section_specializes` [ArkLib/ToMathlib/CoordinateKillBudget.lean:254](../../../ArkLib/ToMathlib/CoordinateKillBudget.lean#L254) vs `CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame.eval_fold_specializes` [ArkLib/Data/CodingTheory/ProximityGap/Hab25FoldFiberCapture.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25FoldFiberCapture.lean#L51)
    - a: Evaluating `Y` at a section then specializing `Z` equals specializing first and evaluating at the sp
    - b: Evaluating `Y` at a section then specializing `Z` equals specializing first and evaluating at the sp
- **1.00** `ArkLib.IteratedFold.foldValOdd` [ArkLib/ToMathlib/IteratedFoldConservation.lean:54](../../../ArkLib/ToMathlib/IteratedFoldConservation.lean#L54) vs `LamLeungTwoPow.foldVal` [ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean:479](../../../ArkLib/Data/CodingTheory/ProximityGap/LamLeungTwoPow.lean#L479)
    - a: The odd folded error values: sums of `v x · x` over squaring fibers.
    - b: The folded error values: sums of `v` over squaring fibers.
- **1.00** `ArkLib.JohnsonList.agree_card_add_hammingDist` [ArkLib/Data/CodingTheory/ProximityGap/JohnsonListBound.lean:132](../../../ArkLib/Data/CodingTheory/ProximityGap/JohnsonListBound.lean#L132) vs `Code.agreementCols_card_add_hammingDist` [ArkLib/Data/CodingTheory/Basic/Distance.lean:178](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean#L178)
    - a: Agreement count plus Hamming distance partitions the coordinate set.
    - b: Agreement count plus Hamming distance partitions the coordinate set.
- **1.00** `ArkLib.ProximityGap.DeepQuotientTransfer.pow_inj_below_order` [ArkLib/Data/CodingTheory/ProximityGap/DeepQuotientTransfer.lean:87](../../../ArkLib/Data/CodingTheory/ProximityGap/DeepQuotientTransfer.lean#L87) vs `ArkLib.ProximityGap.KKH26.pow_inj_lt_orderOf` [ArkLib/Data/CodingTheory/ProximityGap/KKH26StratifiedSpread.lean:394](../../../ArkLib/Data/CodingTheory/ProximityGap/KKH26StratifiedSpread.lean#L394)
    - a: Injectivity of `i ↦ g^i` below the order of `g`, for nonzero `g` in a field. (Local copy of the priv
    - b: Injectivity of `i ↦ g^i` below the order of `g`, for nonzero `g` in a field (local copy of the `priv
- **1.00** `ArkLib.SeqComposeRbrKnowledge.idxToSigma_inl` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:69](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L69) vs `ArkLib.SeqComposeRbrSoundness.idxToSigma_inl` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:91](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L91)
    - a: `seqComposeChallengeIdxToSigma` along the `inl` embedding of a head challenge index lands in the fir
    - b: `seqComposeChallengeIdxToSigma` along the `inl` embedding of a head challenge index lands in the fir
- **1.00** `ArkLib.SeqComposeRbrKnowledge.idxToSigma_inr` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:96](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L96) vs `ArkLib.SeqComposeRbrSoundness.idxToSigma_inr` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:118](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L118)
    - a: `seqComposeChallengeIdxToSigma` along the `inr` embedding of a tail challenge index: the first compo
    - b: `seqComposeChallengeIdxToSigma` along the `inr` embedding of a tail challenge index: the first compo
- **1.00** `ArkLib.SeqComposeRbrKnowledge.seqComposeError_eq_append` [ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean:130](../../../ArkLib/OracleReduction/Composition/Sequential/SeqComposeRbrKnowledgeProof.lean#L130) vs `ArkLib.SeqComposeRbrSoundness.seqComposeError_eq_append` [ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean:152](../../../ArkLib/ProofSystem/Sumcheck/Spec/SeqComposeRbrSoundness.lean#L152)
    - a: **The composed RBR error, indexed via `seqComposeChallengeIdxToSigma` over the global challenge inde
    - b: **The composed RBR error, indexed via `seqComposeChallengeIdxToSigma` over the global challenge inde
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:98](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L98) vs `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:171](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L171)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:98](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L98) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:111](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L111)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:70](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L70) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L140)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:70](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L70) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:99](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L99)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:113](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L113) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:191](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L191)
    - a: Perfect completeness for the full Binary Basefold protocol (reduction)
    - b: Perfect completeness for the full Binary Basefold protocol (reduction)
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:47](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L47) vs `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:114](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L114)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:47](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L47) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:63](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L63)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.hammingDist_le_pair_fiberwiseDistance_mul_two_pow_steps` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorFar.lean:162](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/PreTensorFar.lean#L162) vs `Binius.BinaryBasefold.hammingDist_le_pair_fiberwiseDistance_mul_two_pow_steps_farLiftLocal` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/SoundnessCase2FarLift.lean:321](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/SoundnessCase2FarLift.lean#L321)
    - a: Source Hamming distance is bounded by the number of bad quotient fibers times the fiber size. Local
    - b: Source Hamming distance is bounded by the number of bad quotient fibers times the fiber size. Local
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1441](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1441) vs `RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:492](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L492)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1309](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1309) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1513](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1513)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:668](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L668) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1307](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1307)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1320](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1320) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1516](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1516)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:171](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L171) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:111](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L111)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L140) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:99](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L99)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:114](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L114) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:63](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L63)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `CRTPacketMinpoly.isIntegral_of_pow_eq_one` [ArkLib/Data/CodingTheory/ProximityGap/CRTPacketMinpoly.lean:54](../../../ArkLib/Data/CodingTheory/ProximityGap/CRTPacketMinpoly.lean#L54) vs `ThreadSplit.isIntegral_of_pow_eq_one` [ArkLib/Data/CodingTheory/ProximityGap/ThreadSplit.lean:64](../../../ArkLib/Data/CodingTheory/ProximityGap/ThreadSplit.lean#L64)
    - a: Roots of unity are integral over any base field of the ambient field.
    - b: Roots of unity are integral over any base field of the ambient field.
- **1.00** `CodingTheory.span_inf_ker_proj_of_eq_zero` [ArkLib/Data/CodingTheory/SubspaceDesign.lean:115](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean#L115) vs `CodingTheory.um_span_inf_ker_proj_of_eq_zero` [ArkLib/ToMathlib/UMSubspaceDesignProof.lean:263](../../../ArkLib/ToMathlib/UMSubspaceDesignProof.lean#L263)
    - a: The 1-dimensional subspace `span{a}` meets `ker(proj i)` in itself when `a i = 0`.
    - b: The 1-dimensional subspace `span{a}` meets `ker(proj i)` in itself when `a i = 0`.
- **1.00** `CodingTheory.span_inf_ker_proj_of_ne_zero` [ArkLib/Data/CodingTheory/SubspaceDesign.lean:124](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean#L124) vs `CodingTheory.um_span_inf_ker_proj_of_ne_zero` [ArkLib/ToMathlib/UMSubspaceDesignProof.lean:272](../../../ArkLib/ToMathlib/UMSubspaceDesignProof.lean#L272)
    - a: The 1-dimensional subspace `span{a}` meets `ker(proj i)` trivially when `a i ≠ 0`.
    - b: The 1-dimensional subspace `span{a}` meets `ker(proj i)` trivially when `a i ≠ 0`.
- **1.00** `Commitment.perfectCorrectness` [ArkLib/CommitmentScheme/Basic.lean:109](../../../ArkLib/CommitmentScheme/Basic.lean#L109) vs `CommitmentScheme.perfectCorrectness` [ArkLib/CommitmentScheme/CommitmentScheme.lean:74](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L74)
    - a: A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
    - b: A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
- **1.00** `DeBruijnIntWindowedLaw.int_combination_of_window` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntWindowedLaw.lean:239](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnIntWindowedLaw.lean#L239) vs `DeBruijnWeightedWindowLaw.combination_of_window` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedWindowLaw.lean:277](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnWeightedWindowLaw.lean#L277)
    - a: **The forward direction**, by induction on the window length.
    - b: **The forward direction**, by induction on the window length.
- **1.00** `DeBruijnTwoPrime.packet_mul_coeff` [ArkLib/Data/CodingTheory/ProximityGap/DeBruijnTwoPrime.lean:89](../../../ArkLib/Data/CodingTheory/ProximityGap/DeBruijnTwoPrime.lean#L89) vs `MixedRadixTower.packet_mul_coeff` [ArkLib/Data/CodingTheory/ProximityGap/MixedRadixTower.lean:510](../../../ArkLib/Data/CodingTheory/ProximityGap/MixedRadixTower.lean#L510)
    - a: Slices of a geometric-packet multiple: if `deg R < q` then `(Σ_{i<p} X^(iq) · R).coeff (iq + s) = R.
    - b: Slices of a geometric-packet multiple: if `deg R < q` then `(Σ_{i<p} X^{iq} · R).coeff (iq + s) = R.
- **1.00** `DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L49) vs `DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L286)
    - a: Transport a `List.getElem` along a `Nat` index equality.
    - b: Transport a `List.getElem` along a `Nat` index equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L49) vs `DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L286)
    - a: Transport a `List.getElem` along a `Nat` index equality.
    - b: Transport a `List.getElem` along a `Nat` index equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L49) vs `DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L286)
    - a: Transport a `List.getElem` along a `Nat` index equality.
    - b: Transport a `List.getElem` along a `Nat` index equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_idx_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:49](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L49) vs `DuplexSpongeFS.Sponge316.getElem_idx_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:286](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L286)
    - a: Transport a `List.getElem` along a `Nat` index equality.
    - b: Transport a `List.getElem` along a `Nat` index equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L53) vs `DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L292)
    - a: Transport a `List.getElem` along a list equality.
    - b: Transport a `List.getElem` along a list equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaper.lean#L53) vs `DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L292)
    - a: Transport a `List.getElem` along a list equality.
    - b: Transport a `List.getElem` along a list equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L53) vs `DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L292)
    - a: Transport a `List.getElem` along a list equality.
    - b: Transport a `List.getElem` along a list equality.
- **1.00** `DuplexSpongeFS.Paper.getElem_list_congr` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean:53](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514Paper.lean#L53) vs `DuplexSpongeFS.Sponge316.getElem_list_congrD` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:292](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L292)
    - a: Transport a `List.getElem` along a list equality.
    - b: Transport a `List.getElem` along a list equality.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L354) vs `DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L263)
    - a: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
    - b: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L354) vs `DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L263)
    - a: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
    - b: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L354) vs `DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L263)
    - a: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
    - b: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:354](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L354) vs `DuplexSpongeFS.Sponge316.TimePCounter.dedup_eq'` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:263](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L263)
    - a: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
    - b: Subtype form of `dedup_eq`, used to reduce the `let`-destructuring in the events.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L365) vs `DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L274)
    - a: The combined bad event `E` does NOT fire on the countermodel trace.
    - b: The combined bad event `E` does NOT fire on the countermodel trace.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L365) vs `DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L274)
    - a: The combined bad event `E` does NOT fire on the countermodel trace.
    - b: The combined bad event `E` does NOT fire on the countermodel trace.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L365) vs `DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L274)
    - a: The combined bad event `E` does NOT fire on the countermodel trace.
    - b: The combined bad event `E` does NOT fire on the countermodel trace.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.not_E_trcF` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:365](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L365) vs `DuplexSpongeFS.Sponge316.TimePCounter.not_E_trc` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L274)
    - a: The combined bad event `E` does NOT fire on the countermodel trace.
    - b: The combined bad event `E` does NOT fire on the countermodel trace.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.trcA` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L84) vs `DuplexSpongeFS.Sponge316.ForkCounter.trcB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L87)
    - a: Intermediate trace after erasing slot 2 first.
    - b: Intermediate trace after erasing slot 4 first.
- **1.00** `DuplexSpongeFS.Sponge316.ForkCounter.trcA` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514ForkFalse.lean#L84) vs `DuplexSpongeFS.Sponge316.ForkCounter.trcB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean:87](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkFalse.lean#L87)
    - a: Intermediate trace after erasing slot 2 first.
    - b: Intermediate trace after erasing slot 4 first.
- **1.00** `DuplexSpongeFS.Sponge316.TimePCounter.index_step1` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:130](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L130) vs `DuplexSpongeFS.Sponge316.TimePCounter.index_step2` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:150](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L150)
    - a: The chain index of step 1 (pair `(sA, sB)`) is the raw slot `3`.
    - b: The chain index of step 2 (pair `(sa, sb)`) is the raw slot `1`.
- **1.00** `DuplexSpongeFS.Sponge316.TimePCounter.index_step1` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:130](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L130) vs `DuplexSpongeFS.Sponge316.TimePCounter.index_step2` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:150](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L150)
    - a: The chain index of step 1 (pair `(sA, sB)`) is the raw slot `3`.
    - b: The chain index of step 2 (pair `(sa, sb)`) is the raw slot `1`.
- **1.00** `DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_ASB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L114) vs `DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_asb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L122)
    - a: Entry 3 is the unique trace slot holding either orientation of the pair `(sA, sB)`.
    - b: Entry 1 is the unique trace slot holding either orientation of the pair `(sa, sb)`.
- **1.00** `DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_ASB` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean:114](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TimePFalse.lean#L114) vs `DuplexSpongeFS.Sponge316.TimePCounter.slots_pair_asb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean:122](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma516TimePFalse.lean#L122)
    - a: Entry 3 is the unique trace slot holding either orientation of the pair `(sA, sB)`.
    - b: Entry 1 is the unique trace slot holding either orientation of the pair `(sa, sb)`.
- **1.00** `DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L118) vs `DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L69)
    - a: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
    - b: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- **1.00** `DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ForkPaperFork.lean#L118) vs `DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L69)
    - a: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
    - b: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- **1.00** `DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L118) vs `DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/ConsistencyPaperCascade.lean#L69)
    - a: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
    - b: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- **1.00** `DuplexSpongeFS.Sponge316.firstGuardD_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean:118](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma514PaperFork.lean#L118) vs `DuplexSpongeFS.Sponge316.firstGuard_eraseIdx` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean:69](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512PaperCascade.lean#L69)
    - a: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
    - b: Shifting a "no prior occurrence below `i`" guard through `eraseIdx`.
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:306](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L306) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L203)
    - a: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
    - b: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:306](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L306) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L203)
    - a: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
    - b: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:306](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L306) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L203)
    - a: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
    - b: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:306](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L306) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:203](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L203)
    - a: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
    - b: **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete hash entr
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:227](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L227) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:330](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L330)
    - a: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
    - b: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean:227](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistencyPaper.lean#L227) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:330](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L330)
    - a: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
    - b: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:227](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L227) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean:330](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/HonestConsistency.lean#L330)
    - a: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
    - b: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
- **1.00** `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean:227](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512HonestPaper.lean#L227) vs `DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant_of_mem` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean:330](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/Lemma512Honest.lean#L330)
    - a: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
    - b: Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the deduplica
- **1.00** `GSHasse.gsSupport` [ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean:69](../../../ArkLib/Data/CodingTheory/ProximityGap/GSHasseMultiplicity.lean#L69) vs `GSInterp.gsSupport` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:55](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L55)
    - a: Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
    - b: Monomial support of the GS interpolation space: pairs `(i, j)` with `i + (k-1)·j < D`, organized as
- **1.00** `GSInterp.evalAtPoints` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:133](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L133) vs `R15.evalAtPoints` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean:140](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBound.lean#L140)
    - a: The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
    - b: The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
- **1.00** `GSInterp.evalAtPoints` [ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean:133](../../../ArkLib/Data/CodingTheory/ProximityGap/GSInterpolationExistence.lean#L133) vs `R15.evalAtPoints` [ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean:140](../../../ArkLib/Data/CodingTheory/ProximityGap/SudanListBoundFull.lean#L140)
    - a: The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
    - b: The linear map sending a coefficient vector supported on `S` to the values of the associated bivaria
- **1.00** `Groups.exists_zmod_power_of_generator` [ArkLib/CommitmentScheme/KZG/Algebra.lean:105](../../../ArkLib/CommitmentScheme/KZG/Algebra.lean#L105) vs `KZG.CommitmentScheme.binding_exists_zmod_power_of_generator` [ArkLib/CommitmentScheme/KZG/Binding.lean:167](../../../ArkLib/CommitmentScheme/KZG/Binding.lean#L167)
    - a: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
    - b: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
- **1.00** `Groups.orderOf_eq_prime_of_ne_one` [ArkLib/CommitmentScheme/KZG/Algebra.lean:61](../../../ArkLib/CommitmentScheme/KZG/Algebra.lean#L61) vs `KZG.CommitmentScheme.binding_order_of_eq_prime_of_ne_one` [ArkLib/CommitmentScheme/KZG/Binding.lean:157](../../../ArkLib/CommitmentScheme/KZG/Binding.lean#L157)
    - a: A nontrivial element of a prime-order group has order `p`.
    - b: A nontrivial element of a prime-order group has order `p`.
- **1.00** `IntegerThreadSplit.int_sum_eq_thread_sum` [ArkLib/Data/CodingTheory/ProximityGap/IntegerThreadSplit.lean:40](../../../ArkLib/Data/CodingTheory/ProximityGap/IntegerThreadSplit.lean#L40) vs `WeightedThreadSplit.weighted_sum_eq_thread_sum` [ArkLib/Data/CodingTheory/ProximityGap/WeightedThreadSplit.lean:52](../../../ArkLib/Data/CodingTheory/ProximityGap/WeightedThreadSplit.lean#L52)
    - a: **The ℤ-weighted digit decomposition** (any commutative ring): a ℤ-weighted power sum over `[0, p·m)
    - b: **The weighted digit decomposition** (any commutative ring): an ℕ-weighted power sum over `[0, p·m)`
- **1.00** `IntegerThreadSplit.int_thread_split_iff` [ArkLib/Data/CodingTheory/ProximityGap/IntegerThreadSplit.lean:136](../../../ArkLib/Data/CodingTheory/ProximityGap/IntegerThreadSplit.lean#L136) vs `WeightedThreadSplit.weighted_thread_split_iff` [ArkLib/Data/CodingTheory/ProximityGap/WeightedThreadSplit.lean:148](../../../ArkLib/Data/CodingTheory/ProximityGap/WeightedThreadSplit.lean#L148)
    - a: **ℤ thread-split as an iff**: for `p² ∣ n`, a ℤ-weighted power sum vanishes at `ζ` iff all `p` ℤ-wei
    - b: **Weighted thread-split as an iff**: for `p² ∣ n`, an ℕ-weighted power sum vanishes at `ζ` iff all `
- **1.00** `IntegerThreadSplit.int_vanishing_of_thread_vanishing` [ArkLib/Data/CodingTheory/ProximityGap/IntegerThreadSplit.lean:126](../../../ArkLib/Data/CodingTheory/ProximityGap/IntegerThreadSplit.lean#L126) vs `WeightedThreadSplit.weighted_vanishing_of_thread_vanishing` [ArkLib/Data/CodingTheory/ProximityGap/WeightedThreadSplit.lean:138](../../../ArkLib/Data/CodingTheory/ProximityGap/WeightedThreadSplit.lean#L138)
    - a: **The trivial converse** (pure linearity, any commutative ring).
    - b: **The trivial converse** (pure linearity, any commutative ring).
- **1.00** `KZG.CommitmentScheme.map_binding_instance_drag` [ArkLib/CommitmentScheme/KZG/Binding.lean:639](../../../ArkLib/CommitmentScheme/KZG/Binding.lean#L639) vs `KZG.CommitmentScheme.map_instance_drag` [ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean:534](../../../ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean#L534)
    - a: Transition 3: dragging the map into the probability event.
    - b: Transition 3: dragging the map into the probability event


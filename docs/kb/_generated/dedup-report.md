# ArkLib dedup-candidate report

Generated from `docs/kb/_generated/declarations.json`. **Eyeball, do not auto-rewrite.** The point is to surface name collisions and doc-string overlap that *might* indicate an opportunity to consolidate.

## Stats

- `ArkLib` — 539 files, 10622 declarations

## Same short-name across multiple files (371 groups)

Each group lists declarations sharing a short name across ≥2 files. Most are legitimate (overloaded interface, paper-shape vs general form), but the list is the right anchor to look for duplicates.

### `oracleVerifier` (12 declarations, 11 files)

- `def Binius.RingSwitching.BatchingPhase.oracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:365](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L365) — (no docstring)
- `def CheckClaim.oracleVerifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:197](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L197) — The oracle verifier for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleVerifier` [ArkLib/ProofSystem/Component/DoNothing.lean:72](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L72) — The oracle verifier for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleVerifier` [ArkLib/ProofSystem/Component/RandomQuery.lean:82](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L82) — The oracle verifier simply returns the challenge, and performs no checks.
- `def ReduceClaim.oracleVerifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:200](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L200) — The oracle verifier for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleVerifier` [ArkLib/ProofSystem/Component/SendClaim.lean:63](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L63) — The verifier checks that the relationship `rel oldStmt newStmt` holds. It has access to the original
- `def SendSingleWitness.oracleVerifier` [ArkLib/ProofSystem/Component/SendWitness.lean:217](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L217) — The oracle verifier for the `SendSingleWitness` oracle reduction. The verifier receives the input st
- `def RingSwitching.BatchingPhase.oracleVerifier` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:176](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L176) — (no docstring)
- `def Sumcheck.Spec.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:158](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L158) — The oracle verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:702](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L702) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1350](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1350) — The oracle verifier for the `i`-th round of the sum-check protocol. Migrated to the new `OracleState
- `def ToyProblem.Spec.oracleVerifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:562](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L562) — Oracle verifier for Construction 6.2. Queries the prover's message `g` once and the two oracle codew

### `reduction` (12 declarations, 11 files)

- `def KZG.CommitmentScheme.reduction` [ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean:115](../../../ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean#L115) — The reduction breaking ARSDH using a successful function-binding adversary. The reduction follows th
- `def CheckClaim.reduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:55](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L55) — The reduction for the `CheckClaim` reduction.
- `def DoNothing.reduction` [ArkLib/ProofSystem/Component/DoNothing.lean:43](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L43) — The reduction for the `DoNothing` reduction. - Prover simply returns the statement and witness. - Ve
- `def NoInteraction.reduction` [ArkLib/ProofSystem/Component/NoInteraction.lean:62](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L62) — The no-interaction reduction can be specified by a tuple of functions: - `mapStmt : StmtIn → OracleC
- `def ReduceClaim.reduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:56](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L56) — The reduction for the `ReduceClaim` reduction.
- `def SendWitness.reduction` [ArkLib/ProofSystem/Component/SendWitness.lean:61](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L61) — (no docstring)
- `def Fri.Spec.reduction` [ArkLib/ProofSystem/Fri/Spec/General.lean:107](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L107) — (no docstring)
- `def Sumcheck.Spec.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:168](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L168) — The sum-check protocol as a reduction
- `def Sumcheck.Spec.SingleRound.Simple.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:642](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L642) — The reduction for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1369](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1369) — The sum-check reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Spec.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:485](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L485) — Honest reduction for Construction 6.2: the package `{prover, verifier}` over the bundled-input `Redu
- `def ToyProblem.SimplifiedIOR.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:168](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L168) — Honest reduction for Construction 6.9.

### `pSpec` (12 declarations, 10 files)

- `def RandomQuery.pSpec` [ArkLib/ProofSystem/Component/RandomQuery.lean:53](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L53) — (no docstring)
- `def SendClaim.pSpec` [ArkLib/ProofSystem/Component/SendClaim.lean:31](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L31) — (no docstring)
- `def SendWitness.pSpec` [ArkLib/ProofSystem/Component/SendWitness.lean:39](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L39) — (no docstring)
- `def Fri.Spec.FoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:339](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L339) — Each round of the FRI protocol begins with the verifier sending a random field element as the challe
- `def Fri.Spec.FinalFoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:643](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L643) — The final folding round of the FRI protocol begins with the verifier sending a random field element 
- `def Fri.Spec.QueryRound.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:953](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L953) — (no docstring)
- `def Logup.pSpec` [ArkLib/ProofSystem/Logup/Protocol.lean:80](../../../ArkLib/ProofSystem/Logup/Protocol.lean#L80) — Protocol 2 transcript shape: the outer LogUp messages followed by ArkLib's generic sumcheck.
- `def StirIOP.Round.pSpec` [ArkLib/ProofSystem/Stir/RoundProtocol.lean:60](../../../ArkLib/ProofSystem/Stir/RoundProtocol.lean#L60) — The protocol spec of one STIR fold round: the verifier first sends a folding challenge in `F` (`V_to
- `def Sumcheck.Spec.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:125](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L125) — The protocol specification for the general sum-check protocol, which is the composition of the singl
- `def Sumcheck.Spec.SingleRound.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L149) — The protocol specification for a single round of sum-check. Has the form `⟨!v[.P_to_V, .V_to_P], !v[
- `def ToyProblem.Spec.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:122](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L122) — Protocol specification for Construction 6.2: three rounds, in the order V → P  (γ : F)            --
- `def ToyProblem.SimplifiedIOR.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:108](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L108) — Protocol specification for Construction 6.9: a single `V → P` round sending the combination randomne

### `OracleStatement` (10 declarations, 10 files)

- `abbrev Interaction.OracleStatement` [ArkLib/Interaction/Oracle/Core.lean:91](../../../ArkLib/Interaction/Oracle/Core.lean#L91) — Oracle-statement data for an indexed oracle-statement family.
- `def BatchedFri.Spec.OracleStatement` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:46](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L46) — An oracle for each batched polynomial.
- `def Binius.BinaryBasefold.OracleStatement` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:712](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L712) — For the `i`-th round of the protocol, there will be oracle statements corresponding to all committed
- `def R1CS.OracleStatement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:48](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L48) — (no docstring)
- `def Fri.Spec.OracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:89](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L89) — For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the beginning
- `abbrev Spartan.Spec.OracleStatement` [ArkLib/ProofSystem/Spartan/Basic.lean:60](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L60) — This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R`
- `def StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:84](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L84) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- `def Sumcheck.Spec.OracleStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:136](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L136) — Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of individual 
- `def ToyProblem.Spec.OracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:89](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L89) — Oracle statements of Construction 6.2: the two purported codewords `f₁, f₂ : ι → F`. The verifier on
- `def WhirIOP.OracleStatement` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:146](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L146) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type

### `oracleReduction` (11 declarations, 9 files)

- `def CheckClaim.oracleReduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:205](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L205) — The oracle reduction for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleReduction` [ArkLib/ProofSystem/Component/DoNothing.lean:82](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L82) — The oracle reduction for the `DoNothing` oracle reduction. - Prover simply returns the (non-oracle a
- `def RandomQuery.oracleReduction` [ArkLib/ProofSystem/Component/RandomQuery.lean:100](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L100) — Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction: the input o
- `def ReduceClaim.oracleReduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:217](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L217) — The oracle reduction for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleReduction` [ArkLib/ProofSystem/Component/SendClaim.lean:92](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L92) — Combine the prover and verifier into an oracle reduction. The input has no statement or witness, but
- `def SendSingleWitness.oracleReduction` [ArkLib/ProofSystem/Component/SendWitness.lean:230](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L230) — (no docstring)
- `def Sumcheck.Spec.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:180](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L180) — The sum-check protocol as an oracle reduction
- `def Sumcheck.Spec.SingleRound.Simpler.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:566](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L566) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:721](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L721) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1379](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1379) — The sum-check oracle reduction for the `i`-th round of the sum-check protocol. Migrated to the new `
- `def ToyProblem.Spec.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:594](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L594) — Honest oracle reduction for Construction 6.2: the `OracleProver` / `OracleVerifier` pair packaged as

### `verifier` (11 declarations, 9 files)

- `def CheckClaim.verifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:50](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L50) — The verifier for the `CheckClaim` reduction.
- `def DoNothing.verifier` [ArkLib/ProofSystem/Component/DoNothing.lean:34](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L34) — The verifier for the `DoNothing` reduction.
- `def NoInteraction.verifier` [ArkLib/ProofSystem/Component/NoInteraction.lean:53](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L53) — The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a function
- `def ReduceClaim.verifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:52](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L52) — The verifier for the `ReduceClaim` reduction.
- `def SendWitness.verifier` [ArkLib/ProofSystem/Component/SendWitness.lean:57](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L57) — (no docstring)
- `def Sumcheck.Spec.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L149) — The verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:633](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L633) — The verifier for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1340](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1340) — The verifier for the `i`-th round of the sum-check protocol
- `def Sumcheck.Spec.SingleRound.Unfolded.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1886](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1886) — The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1`
- `def ToyProblem.Spec.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:471](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L471) — Honest verifier for Construction 6.2. Takes the bundled input `(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂
- `def ToyProblem.SimplifiedIOR.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:157](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L157) — Honest verifier for Construction 6.9. Reads `γ` from the transcript and produces the new statement `

### `oracleProver` (10 declarations, 9 files)

- `def Binius.RingSwitching.BatchingPhase.oracleProver` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:326](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L326) — (no docstring)
- `def CheckClaim.oracleProver` [ArkLib/ProofSystem/Component/CheckClaim.lean:184](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L184) — The oracle prover for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleProver` [ArkLib/ProofSystem/Component/DoNothing.lean:67](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L67) — The oracle prover for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleProver` [ArkLib/ProofSystem/Component/RandomQuery.lean:62](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L62) — The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`, a
- `def ReduceClaim.oracleProver` [ArkLib/ProofSystem/Component/ReduceClaim.lean:190](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L190) — The oracle prover for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleProver` [ArkLib/ProofSystem/Component/SendClaim.lean:36](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L36) — The prover takes in the old oracle statement as input, and sends it as the protocol message.
- `def SendWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:133](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L133) — The oracle prover for the `SendWitness` oracle reduction. For each round `i : Fin (FinEnum.card ιw)`
- `def SendSingleWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:201](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L201) — The oracle prover for the `SendSingleWitness` oracle reduction. The prover sends the witness `wit` t
- `def RingSwitching.BatchingPhase.oracleProver` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:128](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L128) — (no docstring)
- `def ToyProblem.Spec.oracleProver` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:514](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L514) — Same as `prover` but exposed at the `OracleProver` signature. The underlying `Prover` is identical (

### `prover` (9 declarations, 8 files)

- `def CheckClaim.prover` [ArkLib/ProofSystem/Component/CheckClaim.lean:39](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L39) — The prover for the `CheckClaim` reduction.
- `def DoNothing.prover` [ArkLib/ProofSystem/Component/DoNothing.lean:30](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L30) — The prover for the `DoNothing` reduction.
- `def NoInteraction.prover` [ArkLib/ProofSystem/Component/NoInteraction.lean:43](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L43) — The prover in a no-interaction reduction can be specified by a tuple of functions: - `mapStmt : Stmt
- `def ReduceClaim.prover` [ArkLib/ProofSystem/Component/ReduceClaim.lean:44](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L44) — The prover for the `ReduceClaim` reduction.
- `def SendWitness.prover` [ArkLib/ProofSystem/Component/SendWitness.lean:47](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L47) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:611](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L611) — The prover in the simple description of a single round of sum-check. Takes in input `target : R` and
- `def Sumcheck.Spec.SingleRound.Unfolded.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1876](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1876) — The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only well-
- `def ToyProblem.Spec.prover` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:427](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L427) — Honest prover for Construction 6.2. After receiving the combination randomness `γ`, the prover sends
- `def ToyProblem.SimplifiedIOR.prover` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:126](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L126) — Honest prover for Construction 6.9. After receiving `γ`, sets the new witness `M_new := M₀ + γ·M₁` a

### `relation` (9 declarations, 8 files)

- `def ArkLib.Lattices.ModuleSIS.relation` [ArkLib/Data/Lattices/ModuleSIS.lean:81](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L81) — The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short, and lies in the k
- `def ConstraintSystem.relation` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:68](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L68) — The underlying set-theoretic relation at a given index.
- `def Lookup.relation` [ArkLib/ProofSystem/ConstraintSystem/Lookup.lean:25](../../../ArkLib/ProofSystem/ConstraintSystem/Lookup.lean#L25) — The lookup relation. Takes in a collection of values and a table, both containers for elements of ty
- `def MemoryChecking.ReadOnly.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:128](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L128) — The read-only memory checking relation. It takes a memory `mem` and a list of read operations `ops`.
- `def MemoryChecking.ReadWrite.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:161](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L161) — The read-write memory checking relation. It takes an initial memory `startMem`, a final memory `fina
- `def Plonk.relation` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:193](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L193) — To define a relation based on the constraint system, we extend it with: - A natural number `ℓ ≤ m` r
- `def R1CS.relation` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:61](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L61) — The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean component-wise 
- `abbrev Spartan.Spec.relation` [ArkLib/ProofSystem/Spartan/Basic.lean:68](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L68) — This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨`
- `def ToyProblem.relation` [ArkLib/ProofSystem/ToyProblem/Definitions.lean:74](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean#L74) — **Definition 6.1 of [ABF26]** (toy problem relation `R_C^ℓ`). Given a base code `C ⊆ (ι → F)` (the p

### `inputRelation` (10 declarations, 7 files)

- `def BatchedFri.Spec.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/General.lean:66](../../../ArkLib/ProofSystem/BatchedFri/Spec/General.lean#L66) — (no docstring)
- `def BatchedFri.Spec.BatchingRound.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:69](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L69) — (no docstring)
- `def Fri.Spec.inputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:46](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L46) — (no docstring)
- `def Fri.Spec.FoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:274](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L274) — The FRI non-final folding round input relation, with proximity parameter `0 < δ`, for the `i`-th rou
- `def Fri.Spec.FinalFoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:582](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L582) — Input relation for the final folding round, with proximity parameter `0 < δ`. The round-`k` codeword
- `def Fri.Spec.QueryRound.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:932](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L932) — (no docstring)
- `def Logup.inputRelation` [ArkLib/ProofSystem/Logup/Common.lean:263](../../../ArkLib/ProofSystem/Logup/Common.lean#L263) — Semantic input relation for Protocol 2: every lookup-column value occurs in the table range.
- `def Sumcheck.Spec.SingleRound.Simpler.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:338](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L338) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:596](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L596) — (no docstring)
- `def ToyProblem.Spec.inputRelation` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:177](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L177) — The IOR-shaped input relation derived from `ToyProblem.relation` (Definition 6.1). `((v, μ₁, μ₂), (f

### `outputRelation` (9 declarations, 6 files)

- `def BatchedFri.Spec.BatchingRound.outputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:84](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L84) — (no docstring)
- `def Fri.Spec.outputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:56](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L56) — (no docstring)
- `def Fri.Spec.FoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:302](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L302) — The FRI non-final folding round output relation, with proximity parameter `0 < δ`, for the `i`-th ro
- `def Fri.Spec.FinalFoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:611](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L611) — Output relation for the final folding round. After the final round the prover sends a polynomial in 
- `def Fri.Spec.QueryRound.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:940](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L940) — (no docstring)
- `def Logup.outputRelation` [ArkLib/ProofSystem/Logup/Common.lean:298](../../../ArkLib/ProofSystem/Logup/Common.lean#L298) — The full protocol has a trivial final relation: successful verification returns `Unit`.
- `def Sumcheck.Spec.SingleRound.Simpler.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:367](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L367) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:599](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L599) — (no docstring)
- `def ToyProblem.Spec.outputRelation` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:256](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L256) — The IOR-shaped *relaxed* output relation derived from `ToyProblem.relaxedRelation` (Definition 6.3).

### `Witness` (6 declarations, 6 files)

- `def BatchedFri.Spec.Witness` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:54](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L54) — The Batched FRI protocol has as witness for each batched polynomial that is supposed to correspond t
- `structure Binius.BinaryBasefold.Witness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:733](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L733) — The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and `Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁'
- `def R1CS.Witness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:51](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L51) — (no docstring)
- `def Fri.Spec.Witness` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:110](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L110) — The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in the
- `abbrev Spartan.Spec.Witness` [ArkLib/ProofSystem/Spartan/Basic.lean:64](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L64) — This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R`
- `def ToyProblem.Spec.Witness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:97](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L97) — Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose encodings are the oracle codeword

### `Statement` (5 declarations, 5 files)

- `def R1CS.Statement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:45](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L45) — (no docstring)
- `def Fri.Spec.Statement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:80](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L80) — For the `i`-th round of the protocol, the input statement is equal to the challenges sent from round
- `abbrev Spartan.Spec.Statement` [ArkLib/ProofSystem/Spartan/Basic.lean:56](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L56) — This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R`
- `structure Sumcheck.Structured.Statement` [ArkLib/ProofSystem/Sumcheck/Structured.lean:197](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L197) — Statement per iterated sumcheck round
- `def ToyProblem.Spec.Statement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:83](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L83) — Input (explicit) statement of Construction 6.2: the linear-constraint vector `v ∈ F^k` and the two c

### `toFinset` (6 declarations, 4 files)

- `def ReedSolomon.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon.lean:97](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L97) — (no docstring)
- `def ReedSolomon.FftDomain.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:184](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L184) — (no docstring)
- `def ReedSolomon.CosetFftDomain.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:552](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L552) — (no docstring)
- `def Domain.CosetFftDomainClass.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:242](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L242) — (no docstring)
- `abbrev Domain.CosetFftDomain.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:258](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L258) — (no docstring)
- `abbrev Domain.FftDomain.toFinset` [ArkLib/Data/Domain/FftDomain/Defs.lean:126](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L126) — (no docstring)

### `StmtIn` (5 declarations, 4 files)

- `def RandomQuery.StmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:30](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L30) — (no docstring)
- `structure Logup.StmtIn` [ArkLib/ProofSystem/Logup/Common.lean:232](../../../ArkLib/ProofSystem/Logup/Common.lean#L232) — Public parameter assumptions for Protocol 2. The paper fixes a finite field with characteristic larg
- `def Sumcheck.Spec.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:137](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L137) — The input statement for the (full) sum-check protocol, which contains only the target sum value
- `def Sumcheck.Spec.SingleRound.Simpler.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:335](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L335) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:585](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L585) — (no docstring)

### `coreInteractionOracleReduction` (4 declarations, 4 files)

- `def coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1090](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1090) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1636](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1636) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def Binius.RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1711](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1711) — Large-field reduction: Sumcheck seqCompose, then append FinalSum
- `def RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1225](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1225) — Large-field reduction: Sumcheck seqCompose, then append FinalSum

### `coreInteractionOracleVerifier` (4 declarations, 4 files)

- `def coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1074](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1074) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1617](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1617) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def Binius.RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1702](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1702) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum
- `def RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1189](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1189) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum

### `disagreementSet` (4 declarations, 4 files)

- `def disagreementSet` [ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean#L63) — The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁. Specialisation of the canonical `Code.disagr
- `def Binius.BinaryBasefold.disagreementSet` [ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean:128](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean#L128) — Disagreement set Δ : The set of points where two functions disagree. For functions f^(i) and g^(i), 
- `def Quotienting.disagreementSet` [ArkLib/ProofSystem/Stir/Quotienting.lean:121](../../../ArkLib/ProofSystem/Stir/Quotienting.lean#L121) — We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S such that 
- `def BlockRelDistance.disagreementSet` [ArkLib/ProofSystem/Whir/BlockRelDistance.lean:104](../../../ArkLib/ProofSystem/Whir/BlockRelDistance.lean#L104) — Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then the (i,k)

### `finalSumcheckKStateProp` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:1666](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L1666) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1336](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1336) — (no docstring)
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1485](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1485) — KState for the final sumcheck step, in the same style as BBF `finalSumcheckKStateProp`: m=0: same as
- `def RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:963](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L963) — (no docstring)

### `finalSumcheckKnowledgeStateFunction` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:1696](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L1696) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1376](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1376) — The knowledge state function for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1513](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1513) — The knowledge state function for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1000](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1000) — The knowledge state function for the final sumcheck step

### `finalSumcheckOracleReduction` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:124](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L124) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:646](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L646) — The oracle reduction for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1256](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1256) — The oracle reduction for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:770](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L770) — The oracle reduction for the final sumcheck step

### `finalSumcheckOracleReduction_perfectCompleteness` (4 declarations, 4 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:139](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L139) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1107](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1107) — Perfect completeness for the final sumcheck step
- `theorem Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1270](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1270) — Perfect completeness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:863](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L863) — Perfect completeness for the final sumcheck step

### `finalSumcheckOracleVerifier_rbrKnowledgeSoundness` (4 declarations, 4 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:1889](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L1889) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1590](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1590) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1650](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1650) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1122](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1122) — Round-by-round knowledge soundness for the final sumcheck step

### `finalSumcheckProver` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckProver` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:64](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L64) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:588](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L588) — The prover for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1198](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1198) — The prover for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:676](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L676) — The prover for the final sumcheck step

### `finalSumcheckRbrExtractor` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:1624](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L1624) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1298](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1298) — The round-by-round extractor for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1462](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1462) — The round-by-round extractor for the final sumcheck step. We do not collapse the witness away (unlik
- `def RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:943](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L943) — The round-by-round extractor for the final sumcheck step

### `finalSumcheckVerifier` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:98](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L98) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:622](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L622) — The verifier for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1229](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1229) — The verifier for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:712](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L712) — The verifier for the final sumcheck step

### `fullOracleProof` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:96](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L96) — The full Binary Basefold protocol as a Proof
- `def Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:171](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L171) — The full Binary Basefold protocol as a Proof
- `def Binius.RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:86](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L86) — The full Binary Basefold protocol as a Proof
- `def RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:96](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L96) — The full Binary Basefold protocol as a Proof

### `fullOracleReduction` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:68](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L68) — The reduction for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L140) — The reduction for the full Binary Basefold protocol
- `def Binius.RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:74](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L74) — The reduction for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:84](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L84) — The reduction for the full Binary Basefold protocol

### `fullOracleReduction_perfectCompleteness` (4 declarations, 4 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:111](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L111) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:191](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L191) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.RingSwitching.FullRingSwitching.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:147](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L147) — (no docstring)
- `theorem RingSwitching.FullRingSwitching.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/General.lean:163](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L163) — (no docstring)

### `fullOracleVerifier` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:45](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L45) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:114](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L114) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:56](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L56) — The oracle verifier for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:60](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L60) — The oracle verifier for the full Binary Basefold protocol

### `fullOracleVerifier_rbrKnowledgeSoundness` (4 declarations, 4 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:143](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L143) — Round-by-round knowledge soundness for the full Binary Basefold oracle verifier
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:237](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L237) — Round-by-round knowledge soundness for the full FRI-Binius oracle verifier.
- `theorem Binius.RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:204](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L204) — Round-by-round knowledge soundness for the full ring-switching oracle verifier
- `theorem RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/General.lean:229](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L229) — Round-by-round knowledge soundness for the full ring-switching oracle verifier. `IsDomain K` (with t

### `fullRbrKnowledgeError` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:133](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L133) — Combined RBR knowledge soundness error for the full protocol
- `def Binius.FRIBinius.FullFRIBinius.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:227](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L227) — Combined RBR knowledge error for full FRI-Binius.
- `def Binius.RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:197](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L197) — (no docstring)
- `def RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/General.lean:217](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L217) — (no docstring)

### `oracleVerifier_rbrKnowledgeSoundness` (4 declarations, 4 files)

- `theorem DoNothing.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:98](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L98) — The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound.
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomQuery.lean:275](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L275) — The `RandomQuery` oracle reduction is round-by-round knowledge sound. The key fact governing the sou
- `theorem ReduceClaim.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:350](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L350) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1216](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1216) — Round-by-round knowledge soundness for the oracle verifier

### `reduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:70](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L70) — The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the input
- `theorem NoInteraction.reduction_completeness` [ArkLib/ProofSystem/Component/NoInteraction.lean:93](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L93) — Completeness of a no-interaction reduction. **Faithfulness of the hypothesis `hRel`.** `Reduction.ru
- `theorem ReduceClaim.reduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:66](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L66) — The `ReduceClaim` reduction satisfies perfect completeness for any relation.
- `theorem SendWitness.reduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:86](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L86) — The `SendWitness` reduction satisfies perfect completeness.

### `simulateQ_simOracle2_messageQuery` (4 declarations, 4 files)

- `lemma Binius.RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:953](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L953) — **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
- `lemma RingSwitching.BatchingPhase.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:59](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L59) — Local message-query collapse for `OracleInterface.simOracle2`.
- `lemma RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1414](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1414) — **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
- `lemma ToyProblem.Spec.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:704](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L704) — `simOracle2` message-query collapse (`OracleComp` form), RIGHT (message) family.

### `completeness` (6 declarations, 3 files)

- `abbrev DuplexSpongeFS.NARG.completeness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:57](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L57) — Paper-facing alias for CO25 Section 3.4 completeness.
- `def Reduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:117](../../../ArkLib/OracleReduction/Security/Basic.lean#L117) — A reduction satisfies **completeness** with regards to: - an initialization function `init : ProbCom
- `def OracleReduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:421](../../../ArkLib/OracleReduction/Security/Basic.lean#L421) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:475](../../../ArkLib/OracleReduction/Security/Basic.lean#L475) — (no docstring)
- `def OracleProof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:504](../../../ArkLib/OracleReduction/Security/Basic.lean#L504) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `theorem SendClaim.completeness` [ArkLib/ProofSystem/Component/SendClaim.lean:110](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L110) — (no docstring)

### `soundness` (6 declarations, 3 files)

- `abbrev DuplexSpongeFS.NARG.soundness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:70](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L70) — Paper-facing alias for CO25 Section 3.4 soundness.
- `def Verifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:295](../../../ArkLib/OracleReduction/Security/Basic.lean#L295) — A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input langua
- `def OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:442](../../../ArkLib/OracleReduction/Security/Basic.lean#L442) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:485](../../../ArkLib/OracleReduction/Security/Basic.lean#L485) — (no docstring)
- `def OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:521](../../../ArkLib/OracleReduction/Security/Basic.lean#L521) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.soundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:127](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L127) — State-restoration soundness

### `subdomain` (6 declarations, 3 files)

- `def ReedSolomon.FftDomain.subdomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:806](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L806) — Given a smooth FFT domain `ω` of log-order `n` this function returns its subdomain of log-order `i`.
- `def ReedSolomon.CosetFftDomain.subdomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1371](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1371) — Given a smooth coset FFT domain `ω` of log-order `n` returns a subdomain of log-order `i`.
- `def Domain.CosetFftDomainClass.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:88](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L88) — Given a smooth coset FFT domain `ω` of log-order `n` this function returns its subdomain of log-orde
- `abbrev Domain.CosetFftDomain.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:427](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L427) — (no docstring)
- `def Domain.FftDomainClass.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:44](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L44) — (no docstring)
- `abbrev Domain.FftDomain.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:134](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L134) — (no docstring)

### `toList` (6 declarations, 3 files)

- `def ReedSolomon.FftDomain.toList` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:287](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L287) — Convert an FFT domain into a list of all its members with proofs the members belong to the FFT domai
- `def ReedSolomon.CosetFftDomain.toList` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:614](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L614) — (no docstring)
- `def Domain.CosetFftDomainClass.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:37](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L37) — (no docstring)
- `def Domain.CosetFftDomain.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:52](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L52) — Convert a coset FFT domain into a list of all its members with proofs the members belong to the FFT 
- `def Domain.FftDomain.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:63](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L63) — Convert a FFT domain into a list of all its members with proofs the members belong to the FFT domain
- `def ProtocolSpec.EncodedMessagesBefore.toList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L77) — Flatten to a sigma-list for consumers still expecting `List (Sigma ...)`.

### `ratchet` (5 declarations, 3 files)

- `def DomainSeparator.ratchet` [ArkLib/Data/Hash/DomainSep.lean:255](../../../ArkLib/Data/Hash/DomainSep.lean#L255) — Ratchet the state. Rust interface: ```rust pub fn ratchet(self) -> Self ```
- `def DuplexSponge.ratchet` [ArkLib/Data/Hash/DuplexSponge.lean:612](../../../ArkLib/Data/Hash/DuplexSponge.lean#L612) — ### Ratchet the sponge state for domain separation Algorithm (from Rust implementation): 1. Permute 
- `def HashStateWithInstructions.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:216](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L216) — Perform a ratchet operation. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainS
- `def FSVerifierState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:347](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L347) — Signal the end of statement with ratcheting. Rust interface: ```rust pub fn ratchet(&mut self) -> Re
- `def FSProverState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:458](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L458) — Ratchet the protocol state. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainSe

### `Adversary` (4 declarations, 3 files)

- `def AGM.Adversary` [ArkLib/AGM/Basic.lean:152](../../../ArkLib/AGM/Basic.lean#L152) — An adversary in the Algebraic Group Model (AGM) is defined as follows: - It is given knowledge of th
- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.Adversary` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:92](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L92) — A weak-binding adversary outputs two weak openings for the same commitment.
- `abbrev ArkLib.Lattices.SIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:53](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L53) — A search adversary for a SIS-style problem.
- `abbrev ArkLib.Lattices.ModuleSIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:96](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L96) — A Module-SIS adversary.

### `OStmtIn` (4 declarations, 3 files)

- `def RandomQuery.OStmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:33](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L33) — (no docstring)
- `def Logup.OStmtIn` [ArkLib/ProofSystem/Logup/Common.lean:240](../../../ArkLib/ProofSystem/Logup/Common.lean#L240) — Input oracle statements: the table `t` and lookup columns `fᵢ`, as multilinear oracles.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:336](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L336) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:591](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L591) — (no docstring)

### `OStmtOut` (4 declarations, 3 files)

- `def RandomQuery.OStmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:34](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L34) — (no docstring)
- `def Logup.OStmtOut` [ArkLib/ProofSystem/Logup/Common.lean:289](../../../ArkLib/ProofSystem/Logup/Common.lean#L289) — Output oracle statements for the full LogUp protocol.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:365](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L365) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:594](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L594) — (no docstring)

### `StmtOut` (4 declarations, 3 files)

- `def RandomQuery.StmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:31](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L31) — (no docstring)
- `def Logup.StmtOut` [ArkLib/ProofSystem/Logup/Common.lean:279](../../../ArkLib/ProofSystem/Logup/Common.lean#L279) — The full LogUp protocol returns no additional public data on success.
- `def Sumcheck.Spec.SingleRound.Simpler.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:364](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L364) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:588](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L588) — (no docstring)

### `correctness` (4 declarations, 3 files)

- `def Commitment.correctness` [ArkLib/CommitmentScheme/Basic.lean:88](../../../ArkLib/CommitmentScheme/Basic.lean#L88) — A commitment scheme satisfies **correctness** with error `correctnessError` if for all `data : Data`
- `def CommitmentScheme.correctness` [ArkLib/CommitmentScheme/CommitmentScheme.lean:64](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L64) — A commitment scheme satisfies **correctness** with error `correctnessError` if, for every message, t
- `theorem KZG.correctness` [ArkLib/CommitmentScheme/KZG/Correctness.lean:51](../../../ArkLib/CommitmentScheme/KZG/Correctness.lean#L51) — Algebraic correctness of one KZG opening for a coefficient vector.
- `theorem KZG.CommitmentScheme.correctness` [ArkLib/CommitmentScheme/KZG/Correctness.lean:161](../../../ArkLib/CommitmentScheme/KZG/Correctness.lean#L161) — The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

### `drop` (4 declarations, 3 files)

- `def Fin.drop` [ArkLib/Data/Fin/Tuple/Defs.lean:60](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L60) — Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.
- `def ProtocolSpec.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:127](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L127) — Drop the first `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:184](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L184) — (no docstring)
- `def SumcheckDomain.drop` [ArkLib/ProofSystem/Sumcheck/Domain.lean:133](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L133) — Drop the first `j` coordinates, leaving the domain on the remaining `k - j` coordinates: coordinate 

### `injOn` (4 declarations, 3 files)

- `lemma ReedSolomon.FftDomain.injOn` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:345](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L345) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.injOn` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:646](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L646) — (no docstring)
- `lemma Domain.CosetFftDomain.injOn` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:233](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L233) — (no docstring)
- `lemma Domain.FftDomain.injOn` [ArkLib/Data/Domain/FftDomain/Defs.lean:116](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L116) — (no docstring)

### `injective` (4 declarations, 3 files)

- `lemma ReedSolomon.FftDomain.injective` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:340](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L340) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.injective` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:639](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L639) — (no docstring)
- `lemma Domain.CosetFftDomain.injective` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:228](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L228) — (no docstring)
- `lemma Domain.FftDomain.injective` [ArkLib/Data/Domain/FftDomain/Defs.lean:112](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L112) — (no docstring)

### `Message` (3 declarations, 3 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Message` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:122](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L122) — Messages: block vectors over the message row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Message` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:32](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L32) — Messages: column vectors over `Rq Φ`.
- `def ProtocolSpec.Message` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:76](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L76) — The type of the `i`-th message in a protocol specification. This does not distinguish between messag

### `Opening` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.Opening` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:98](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L98) — A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)` (`Decomp`) ext
- `abbrev ArkLib.Lattices.Ajtai.Simple.Opening` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:43](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L43) — The simple Ajtai commitment has no auxiliary opening data.
- `structure Commitment.Opening` [ArkLib/CommitmentScheme/Basic.lean:59](../../../ArkLib/CommitmentScheme/Basic.lean#L59) — The opening protocol used to prove a claimed oracle response for committed data.

### `OutputStatement` (3 declarations, 3 files)

- `abbrev Sumcheck.Spec.OutputStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:131](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L131) — (no docstring)
- `def ToyProblem.Spec.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:102](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L102) — Output statement: the IOR is a yes/no test — accept (return `()`) or short-circuit to `none` via `Op
- `def ToyProblem.SimplifiedIOR.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:72](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L72) — Output statement for C6.9: the new `(v, μ_new)` pair. The constraint count drops from 2 to 1 (a sing

### `Params` (3 declarations, 3 files)

- `structure Poseidon2.Params` [ArkLib/Data/Hash/Poseidon2.lean:412](../../../ArkLib/Data/Hash/Poseidon2.lean#L412) — The parameters determining a Poseidon2 permutation (over the KoalaBear field)
- `structure StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:35](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L35) — **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun
- `structure WhirIOP.Params` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:54](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L54) — ** Per‑round protocol parameters. ** For a fixed depth `M`, the reduction runs `M + 1` rounds. In ro

### `Prover` (4 declarations, 3 files)

- `abbrev Interaction.Oracle.Prover` [ArkLib/Interaction/Oracle/Core.lean:1131](../../../ArkLib/Interaction/Oracle/Core.lean#L1131) — Oracle prover on `Oracle.Spec`: given ambient input `shared`, local statement/oracle data and witnes
- `abbrev Interaction.Prover` [ArkLib/Interaction/Reduction.lean:101](../../../ArkLib/Interaction/Reduction.lean#L101) — A prover: given ambient input `i`, local statement `stmt`, and local witness `wit`, performs monadic
- `structure Prover` [ArkLib/OracleReduction/Basic.lean:168](../../../ArkLib/OracleReduction/Basic.lean#L168) — (no docstring)
- `structure Prover` [ArkLib/OracleReduction/Basic.lean:413](../../../ArkLib/OracleReduction/Basic.lean#L413) — The type of honest provers for an interactive reduction with `n` messages. This consists of: - `PrvS

### `PublicParams` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.PublicParams` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:77](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L77) — Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`.
- `abbrev ArkLib.Lattices.Ajtai.Simple.PublicParams` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:29](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L29) — Public parameters: the Ajtai matrix `A`.
- `structure Spartan.PublicParams` [ArkLib/ProofSystem/Spartan/Basic.lean:26](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L26) — The public parameters of the (padded) Spartan protocol. Consists of the number of bits of the R1CS d

### `Reduction` (3 declarations, 3 files)

- `structure Interaction.Oracle.Reduction` [ArkLib/Interaction/Oracle/Core.lean:1208](../../../ArkLib/Interaction/Oracle/Core.lean#L1208) — Oracle reduction on `Oracle.Spec`: bundles a prover and a verifier for the same protocol. The prover
- `structure Interaction.Reduction` [ArkLib/Interaction/Reduction.lean:171](../../../ArkLib/Interaction/Reduction.lean#L171) — A reduction pairs a prover with a verifier for the same protocol.
- `structure Reduction` [ArkLib/OracleReduction/Basic.lean:639](../../../ArkLib/OracleReduction/Basic.lean#L639) — An **interactive reduction** for a given protocol specification `pSpec`, and relative to oracles def

### `StraightlineExtractor` (3 declarations, 3 files)

- `abbrev Commitment.StraightlineExtractor` [ArkLib/CommitmentScheme/Basic.lean:178](../../../ArkLib/CommitmentScheme/Basic.lean#L178) — A **straightline extractor** for a commitment scheme takes in the commitment, the log of queries mad
- `def CommitmentScheme.StraightlineExtractor` [ArkLib/CommitmentScheme/CommitmentScheme.lean:123](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L123) — A **straightline extractor** for a standard commitment scheme takes the commitment and the log of qu
- `abbrev DuplexSpongeFS.NARG.StraightlineExtractor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:84](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L84) — Paper-facing alias for the straightline extractor interface used in Section 3.4.

### `SumcheckWitness` (3 declarations, 3 files)

- `abbrev Binius.RingSwitching.SumcheckWitness` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:226](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L226) — (no docstring)
- `abbrev RingSwitching.SumcheckWitness` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:236](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L236) — (no docstring)
- `structure Sumcheck.Structured.SumcheckWitness` [ArkLib/ProofSystem/Sumcheck/Structured.lean:231](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L231) — Witness for the structured sumcheck at round `i`: - `t'` — the original multilinear polynomial (the 

### `Verifier` (3 declarations, 3 files)

- `structure Interaction.Oracle.Verifier` [ArkLib/Interaction/Oracle/Core.lean:1171](../../../ArkLib/Interaction/Oracle/Core.lean#L1171) — Oracle verifier on `Oracle.Spec`: the interactive verifier (`toFun`) and output-oracle simulation (`
- `abbrev Interaction.Verifier` [ArkLib/Interaction/Reduction.lean:115](../../../ArkLib/Interaction/Reduction.lean#L115) — A verifier: given ambient input `i` and local statement `stmt`, provides a `Counterpart` with `State
- `structure Verifier` [ArkLib/OracleReduction/Basic.lean:438](../../../ArkLib/OracleReduction/Basic.lean#L438) — A verifier of an interactive protocol is a function that takes in the input statement and the transc

### `absorb` (3 declarations, 3 files)

- `def DomainSeparator.absorb` [ArkLib/Data/Hash/DomainSep.lean:216](../../../ArkLib/Data/Hash/DomainSep.lean#L216) — Absorb `count` native elements. Rust interface: ```rust pub fn absorb(self, count: usize, label: &st
- `def DuplexSponge.absorb` [ArkLib/Data/Hash/DuplexSponge.lean:416](../../../ArkLib/Data/Hash/DuplexSponge.lean#L416) — ### Absorb a list of units into the sponge (paper version) Paper algorithm (process one element at a
- `def HashStateWithInstructions.absorb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:109](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L109) — Perform secure absorption of elements into the sponge. Rust interface: ```rust pub fn absorb(&mut se

### `batchingCoreRbrKnowledgeError` (3 declarations, 3 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:217](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L217) — Combined RBR knowledge error for batching + core interaction.
- `def Binius.RingSwitching.FullRingSwitching.batchingCoreRbrKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:191](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L191) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/General.lean:211](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L211) — (no docstring)

### `batchingCoreReduction` (3 declarations, 3 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:95](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L95) — (no docstring)
- `def Binius.RingSwitching.FullRingSwitching.batchingCoreReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:63](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L63) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:66](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L66) — (no docstring)

### `batchingCoreVerifier` (3 declarations, 3 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:77](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L77) — (no docstring)
- `def Binius.RingSwitching.FullRingSwitching.batchingCoreVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:46](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L46) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:42](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L42) — (no docstring)

### `binding` (3 declarations, 3 files)

- `def Commitment.binding` [ArkLib/CommitmentScheme/Basic.lean:170](../../../ArkLib/CommitmentScheme/Basic.lean#L170) — A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all adversar
- `def CommitmentScheme.binding` [ArkLib/CommitmentScheme/CommitmentScheme.lean:104](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L104) — A commitment scheme satisfies **binding** with error `bindingError` if every adversary's probability
- `theorem KZG.CommitmentScheme.binding` [ArkLib/CommitmentScheme/KZG/Binding.lean:737](../../../ArkLib/CommitmentScheme/KZG/Binding.lean#L737) — The KZG scheme satisfies evaluation binding provided `t`-SDH holds.

### `coeffHom` (3 declarations, 3 files)

- `def ProximityPrize.BCIKS20.GammaGenuine.coeffHom` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/GammaGenuine.lean:87](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/GammaGenuine.lean#L87) — The per-`Y`-coefficient ring hom `F[X][Y] → (𝕃 H)⟦X⟧`: recenter the `X`-layer at `x₀` (`taylorAlgHom
- `def ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:175](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L175) — Reading off the `k`-th coefficient of the underlying polynomial, as an additive homomorphism `Rq Φ →
- `def CompPoly.CPolynomial.coeffHom` [ArkLib/ToCompPoly/Univariate/Basic.lean:284](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L284) — Extracting the `k`-th coefficient as an additive homomorphism.

### `coeff_pow_sub_at` (3 declarations, 3 files)

- `theorem ProximityPrize.HenselExistence.coeff_pow_sub_at` [ArkLib/Data/Polynomial/HenselExistence.lean:88](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L88) — Local copy of `NewtonLinearization.coeff_pow_sub_at` (order-`t` Newton linearization).
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_pow_sub_at` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:93](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L93) — **LEMMA B (Newton power linearization).** Local copy of `NewtonLinearization.coeff_pow_sub_at`.
- `theorem ProximityPrize.NewtonLinearization.coeff_pow_sub_at` [ArkLib/Data/Polynomial/NewtonLinearization.lean:97](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L97) — **Newton linearization at order `t`.** Under the below-`t` agreement hypothesis with `0 < t`, writin

### `coeff_pow_sub_below` (3 declarations, 3 files)

- `theorem ProximityPrize.HenselExistence.coeff_pow_sub_below` [ArkLib/Data/Polynomial/HenselExistence.lean:71](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L71) — Local copy of `NewtonLinearization.coeff_pow_sub_below` (truncation propagation).
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_pow_sub_below` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:75](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L75) — **LEMMA A (truncation propagation).** Agreement below order `t` propagates to every power. Local cop
- `theorem ProximityPrize.NewtonLinearization.coeff_pow_sub_below` [ArkLib/Data/Polynomial/NewtonLinearization.lean:61](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L61) — **Truncation propagation.** If `γ₁ γ₂ : R⟦X⟧` agree at every coefficient `j < t`, then so do `γ₁^i` 

### `commit` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.Simple.commit` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:38](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L38) — Deterministically commit by multiplying the public matrix by the message vector.
- `def KZG.commit` [ArkLib/CommitmentScheme/KZG/Basic.lean:55](../../../ArkLib/CommitmentScheme/KZG/Basic.lean#L55) — To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of maximum deg
- `def SimpleRO.commit` [ArkLib/CommitmentScheme/SimpleRO.lean:43](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L43) — (no docstring)

### `commitmentScheme` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commitmentScheme` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:200](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L200) — The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound weak ver
- `def ArkLib.Lattices.Ajtai.Simple.commitmentScheme` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:56](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L56) — The simple Ajtai commitment as a `CommitmentScheme`. An opening is accepted only when the message sa
- `def SimpleRO.commitmentScheme` [ArkLib/CommitmentScheme/SimpleRO.lean:83](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L83) — (no docstring)

### `finalSumcheckKnowledgeError` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:316](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L316) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1287](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1287) — RBR knowledge error for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1454](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1454) — RBR knowledge error for the final sumcheck step

### `finalSumcheckStepLogic` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:908](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L908) — The Logic Instance for the final sumcheck step. This is a 1-message protocol where the prover sends 
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:555](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L555) — The logic instance for the FRI final sumcheck step.
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:994](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L994) — The Logic Instance for the final sumcheck step. This is a 1-message protocol where the prover sends 

### `finalSumcheckStep_is_logic_complete` (3 declarations, 3 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_is_logic_complete` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1358](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1358) — Final sumcheck step logic is strongly complete. **Key Proof Obligations:** 1. **Verifier Check**: Sh
- `lemma Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_is_logic_complete` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1054](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1054) — Strong completeness of the FRI final sumcheck logic step.
- `lemma Binius.RingSwitching.SumcheckPhase.finalSumcheckStep_is_logic_complete` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1146](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1146) — Final sumcheck step logic is strongly complete. **Key Proof Obligations:** 1. **Verifier Check**: Sh

### `finalSumcheckStep_verifierCheck_passed` (3 declarations, 3 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1219](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1219) — The verifier check passes in the final sumcheck step. **Proof structure:** 1. From `sumcheckConsiste
- `lemma Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:969](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L969) — Verifier check passes in the FRI final sumcheck logic step.
- `lemma Binius.RingSwitching.SumcheckPhase.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1087](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1087) — **Main helper lemma**: The verifier check passes in the final sumcheck step. **Proof Structure** (fo

### `fullPspec` (3 declarations, 3 files)

- `def Binius.FRIBinius.FullFRIBinius.fullPspec` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:54](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L54) — (no docstring)
- `def Binius.RingSwitching.fullPspec` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:76](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L76) — (no docstring)
- `def RingSwitching.fullPspec` [ArkLib/ProofSystem/RingSwitching/Spec.lean:57](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L57) — (no docstring)

### `knowledgeStateFunction` (3 declarations, 3 files)

- `def CheckClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/CheckClaim.lean:127](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L127) — The knowledge state function for the `CheckClaim` reduction. Since there is no challenge round, the 
- `def RandomQuery.knowledgeStateFunction` [ArkLib/ProofSystem/Component/RandomQuery.lean:230](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L230) — The knowledge state function for the `RandomQuery` oracle reduction.
- `def ReduceClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:138](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L138) — The knowledge state function for the `ReduceClaim` reduction.

### `masterKStateProp` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.masterKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1320](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1320) — Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event of the `i-th` oracle if
- `def Binius.RingSwitching.masterKStateProp` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:430](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L430) — (no docstring)
- `def RingSwitching.masterKStateProp` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:444](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L444) — (no docstring)

### `oracleReduction_completeness` (3 declarations, 3 files)

- `theorem RandomQuery.oracleReduction_completeness` [ArkLib/ProofSystem/Component/RandomQuery.lean:114](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L114) — The `RandomQuery` oracle reduction is perfectly complete.
- `theorem ReduceClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:233](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L233) — The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. Proof strategy m
- `theorem SendSingleWitness.oracleReduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:275](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L275) — The `SendSingleWitness` oracle reduction satisfies perfect completeness.

### `oracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem DoNothing.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:92](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L92) — The `DoNothing` oracle reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1033](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1033) — Perfect completeness for the oracle reduction
- `theorem ToyProblem.Spec.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:931](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L931) — **Honest completeness for Construction 6.2** (protocol-level form). The honest oracle reduction is p

### `pSpecCoreInteraction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:248](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L248) — (no docstring)
- `def Binius.RingSwitching.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:70](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L70) — (no docstring)
- `def RingSwitching.pSpecCoreInteraction` [ArkLib/ProofSystem/RingSwitching/Spec.lean:50](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L50) — (no docstring)

### `pSpecSumcheckRound` (3 declarations, 3 files)

- `def Binius.RingSwitching.pSpecSumcheckRound` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:61](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L61) — (no docstring)
- `abbrev RingSwitching.pSpecSumcheckRound` [ArkLib/ProofSystem/RingSwitching/Spec.lean:41](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L41) — (no docstring)
- `def Sumcheck.Structured.pSpecSumcheckRound` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:148](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L148) — Protocol spec for one round of the structured sumcheck: P sends a degree-≤`d` univariate `h_i(X) ∈ L

### `relOut` (3 declarations, 3 files)

- `def CheckClaim.relOut` [ArkLib/ProofSystem/Component/CheckClaim.lean:63](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L63) — (no docstring)
- `def RandomQuery.relOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:49](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L49) — The output relation states that if the verifier's single query was `q`, then `a` and `b` agree on th
- `def SendClaim.relOut` [ArkLib/ProofSystem/Component/SendClaim.lean:98](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L98) — (no docstring)

### `simulateQ_simOracle2_query` (3 declarations, 3 files)

- `lemma Binius.RingSwitching.simulateQ_simOracle2_query` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:975](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L975) — **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as `simulateQ_s
- `lemma RingSwitching.BatchingPhase.simulateQ_simOracle2_query` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:77](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L77) — OptionT/query form of `simulateQ_simOracle2_messageQuery`.
- `lemma RingSwitching.simulateQ_simOracle2_query` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1436](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1436) — **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as `simulateQ_s

### `squeeze` (3 declarations, 3 files)

- `def DomainSeparator.squeeze` [ArkLib/Data/Hash/DomainSep.lean:241](../../../ArkLib/Data/Hash/DomainSep.lean#L241) — Squeeze `count` native elements. Rust interface: ```rust pub fn squeeze(self, count: usize, label: &
- `def DuplexSponge.squeeze` [ArkLib/Data/Hash/DuplexSponge.lean:512](../../../ArkLib/Data/Hash/DuplexSponge.lean#L512) — ### Squeeze out a vector of units from the sponge (paper version) We differ from the paper version i
- `def HashStateWithInstructions.squeeze` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:148](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L148) — Perform a secure squeeze operation. Rust interface: ```rust pub fn squeeze(&mut self, output: &mut [

### `toVerifier` (3 declarations, 3 files)

- `def Interaction.OracleDecoration.OracleReduction.toVerifier` [ArkLib/Interaction/Oracle/Core.lean:1087](../../../ArkLib/Interaction/Oracle/Core.lean#L1087) — Forget the prover and witness bookkeeping of an oracle reduction, keeping only the verifier-side int
- `def Interaction.PublicCoinVerifier.toVerifier` [ArkLib/Interaction/Reduction.lean:146](../../../ArkLib/Interaction/Reduction.lean#L146) — Forget that a verifier is public-coin and view it as an ordinary verifier.
- `def OracleVerifier.toVerifier` [ArkLib/OracleReduction/Basic.lean:516](../../../ArkLib/OracleReduction/Basic.lean#L516) — An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface using it

### `verify` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.Simple.verify` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:46](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L46) — Verify a simple Ajtai opening by checking the matrix product.
- `def SimpleRO.verify` [ArkLib/CommitmentScheme/SimpleRO.lean:50](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L50) — (no docstring)
- `def OracleVerifier.Append.verify` [ArkLib/OracleReduction/Composition/Sequential/Append.lean:371](../../../ArkLib/OracleReduction/Composition/Sequential/Append.lean#L371) — The composite `verify`: run `V₁` (routed by `router₁`) to obtain the intermediate statement, then ru

### `witnessStructuralInvariant` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1081](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1081) — This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
- `def Binius.RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:423](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L423) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- `def RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:437](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L437) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`

### `cast_id` (9 declarations, 2 files)

- `theorem Prover.cast_id` [ArkLib/OracleReduction/Cast.lean:53](../../../ArkLib/OracleReduction/Cast.lean#L53) — (no docstring)
- `theorem OracleProver.cast_id` [ArkLib/OracleReduction/Cast.lean:77](../../../ArkLib/OracleReduction/Cast.lean#L77) — (no docstring)
- `theorem Verifier.cast_id` [ArkLib/OracleReduction/Cast.lean:99](../../../ArkLib/OracleReduction/Cast.lean#L99) — (no docstring)
- `theorem Reduction.cast_id` [ArkLib/OracleReduction/Cast.lean:284](../../../ArkLib/OracleReduction/Cast.lean#L284) — (no docstring)
- `theorem ProtocolSpec.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:35](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L35) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:79](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L79) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:118](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L118) — (no docstring)
- `theorem ProtocolSpec.Transcript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:162](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L162) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:188](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L188) — (no docstring)

### `seqCompose` (8 declarations, 2 files)

- `def Prover.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:37](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L37) — Sequential composition of provers, defined via iteration of the composition (append) of two provers.
- `def Verifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:75](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L75) — Sequential composition of verifiers, defined via iteration of the composition (append) of two verifi
- `def Reduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:104](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L104) — Sequential composition of reductions, defined via sequential composition of provers and verifiers (o
- `def OracleProver.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:135](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L135) — Sequential composition of provers in oracle reductions, defined via sequential composition of prover
- `def OracleVerifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:188](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L188) — Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the comp
- `def OracleReduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:310](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L310) — Sequential composition of oracle reductions, defined via sequential composition of oracle provers an
- `def ProtocolSpec.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:300](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L300) — Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`. Defined for definitio
- `def ProtocolSpec.FullTranscript.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:358](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L358) — Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`. Defined for definit

### `seqCompose_zero` (7 declarations, 2 files)

- `lemma Prover.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:48](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L48) — (no docstring)
- `lemma Verifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:83](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L83) — (no docstring)
- `lemma Reduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:113](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L113) — (no docstring)
- `lemma OracleVerifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:204](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L204) — (no docstring)
- `lemma OracleReduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:347](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L347) — (no docstring)
- `theorem ProtocolSpec.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:316](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L316) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:363](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L363) — (no docstring)

### `concat` (5 declarations, 2 files)

- `def ProtocolSpec.MessagesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:414](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L414) — Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming round `
- `def ProtocolSpec.ChallengesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:463](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L463) — Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming rou
- `abbrev ProtocolSpec.Transcript.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:502](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L502) — Concatenate a message to the end of a partial transcript. This is definitionally equivalent to `Fin.
- `abbrev ProtocolSpec.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:41](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L41) — Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec`
- `def ProtocolSpec.FullTranscript.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:165](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L165) — Adding a message with a given direction and type to the end of a `Transcript`

### `knowledgeSoundness` (5 declarations, 2 files)

- `def Verifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:328](../../../ArkLib/OracleReduction/Security/Basic.lean#L328) — A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and wit
- `def OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:450](../../../ArkLib/OracleReduction/Security/Basic.lean#L450) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:491](../../../ArkLib/OracleReduction/Security/Basic.lean#L491) — (no docstring)
- `def OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:529](../../../ArkLib/OracleReduction/Security/Basic.lean#L529) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.knowledgeSoundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:141](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L141) — State-restoration knowledge soundness (w/ straightline extractor).

### `log` (5 declarations, 2 files)

- `def ReedSolomon.FftDomain.log` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:737](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L737) — Finds a preimage of `x` under the mapping `ω`.
- `def ReedSolomon.CosetFftDomain.log` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1332](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1332) — Finds a preimage of `x` under the mapping `ω`.
- `def Domain.CosetFftDomainClass.log` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:45](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L45) — Finds a preimage of `x` under the mapping `ω`.
- `abbrev Domain.CosetFftDomain.log` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:75](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L75) — (no docstring)
- `abbrev Domain.FftDomain.log` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:82](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L82) — (no docstring)

### `new` (5 declarations, 2 files)

- `def DomainSeparator.Op.new` [ArkLib/Data/Hash/DomainSep.lean:138](../../../ArkLib/Data/Hash/DomainSep.lean#L138) — Construct a new `Op` from a character `id` and a count number `count : Option Nat`. Returns error if
- `def DomainSeparator.new` [ArkLib/Data/Hash/DomainSep.lean:193](../../../ArkLib/Data/Hash/DomainSep.lean#L193) — Create a new DomainSeparator with the domain separator. Rust interface: ```rust pub fn new(session_i
- `def HashStateWithInstructions.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:97](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L97) — Initialize a stateful hash object from a domain separator. Rust interface: ```rust pub fn new(domain
- `def FSVerifierState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:274](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L274) — Create a new VerifierState from a domain separator and NARG string. Rust interface: ```rust pub fn n
- `def FSProverState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:415](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L415) — Create a new `FSProverState` from a domain separator and RNG. Rust interface: ```rust pub fn new(dom

### `perfectCompleteness` (5 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.perfectCompleteness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:64](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L64) — Paper-facing alias for CO25 Section 3.4 perfect completeness.
- `def Reduction.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:126](../../../ArkLib/OracleReduction/Security/Basic.lean#L126) — A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`.
- `def OracleReduction.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:430](../../../ArkLib/OracleReduction/Security/Basic.lean#L430) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:480](../../../ArkLib/OracleReduction/Security/Basic.lean#L480) — (no docstring)
- `def OracleProof.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:513](../../../ArkLib/OracleReduction/Security/Basic.lean#L513) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.

### `cast_eq_dcast₂` (4 declarations, 2 files)

- `theorem Verifier.cast_eq_dcast₂` [ArkLib/OracleReduction/Cast.lean:107](../../../ArkLib/OracleReduction/Cast.lean#L107) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:91](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L91) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:130](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L130) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:194](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L194) — (no docstring)

### `instDCast₂` (4 declarations, 2 files)

- `instance Prover.instDCast₂` [ArkLib/OracleReduction/Cast.lean:60](../../../ArkLib/OracleReduction/Cast.lean#L60) — (no docstring)
- `instance ProtocolSpec.MessageIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:87](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L87) — (no docstring)
- `instance ProtocolSpec.ChallengeIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:126](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L126) — (no docstring)
- `instance ProtocolSpec.FullTranscript.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:190](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L190) — (no docstring)

### `accepts` (3 declarations, 2 files)

- `def Plonk.Gate.accepts` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:58](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L58) — A gate accepts an input vector `x` if its evaluation at `x` is zero.
- `def Plonk.ConstraintSystem.accepts` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:129](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L129) — A constraint system accepts an input vector `x` if all of its gates accept `x`.
- `def ToyProblem.Spec.accepts` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:166](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L166) — The §6.1 decision predicate, factored out so completeness proofs and the verifier object share the s

### `advantage` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.advantage` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:409](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L409) — Weak-binding advantage.
- `def ArkLib.Lattices.SIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:62](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L62) — Search advantage for a SIS-style problem.
- `def ArkLib.Lattices.ModuleSIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:108](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L108) — The Module-SIS advantage.

### `append` (3 declarations, 2 files)

- `def Interaction.Oracle.Spec.append` [ArkLib/Interaction/Oracle/Spec.lean:207](../../../ArkLib/Interaction/Oracle/Spec.lean#L207) — Sequential composition of `Oracle.Spec`: run `s₁` first, then continue with `s₂ pt₁` where `pt₁ : Pu
- `abbrev ProtocolSpec.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:46](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L46) — Appending two `ProtocolSpec`s
- `def ProtocolSpec.FullTranscript.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:157](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L157) — Appending two transcripts for two `ProtocolSpec`s

### `experiment` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.experiment` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:396](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L396) — The Hachi/Greyhound weak-binding experiment. ## Ordinary vs. weak binding *Ordinary (exact) binding*
- `def ArkLib.Lattices.SIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:56](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L56) — The SIS experiment: sample a challenge, run the adversary, check validity.
- `def ArkLib.Lattices.ModuleSIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:102](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L102) — The Module-SIS experiment.

### `extract` (3 declarations, 2 files)

- `def Fin.extract` [ArkLib/Data/Fin/Tuple/Defs.lean:73](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L73) — Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`.
- `def ProtocolSpec.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:135](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L135) — Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`.
- `abbrev ProtocolSpec.FullTranscript.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:192](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L192) — (no docstring)

### `logAux` (3 declarations, 2 files)

- `def ReedSolomon.FftDomain.logAux` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:727](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L727) — (no docstring)
- `def ReedSolomon.CosetFftDomain.logAux` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1322](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1322) — (no docstring)
- `def Domain.CosetFftDomainClass.logAux` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:35](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L35) — (no docstring)

### `log_left_inverse` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.log_left_inverse` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:760](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L760) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.log_left_inverse` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1355](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1355) — (no docstring)
- `lemma Domain.CosetFftDomainClass.log_left_inverse` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:67](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L67) — (no docstring)

### `log_right_inverse` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.log_right_inverse` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:757](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L757) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.log_right_inverse` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1352](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1352) — (no docstring)
- `lemma Domain.CosetFftDomainClass.log_right_inverse` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:64](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L64) — (no docstring)

### `log_right_inverse'` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.log_right_inverse'` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:741](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L741) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.log_right_inverse'` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1336](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1336) — (no docstring)
- `lemma Domain.CosetFftDomainClass.log_right_inverse'` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:48](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L48) — (no docstring)

### `mem_subdomain_of_eq_vals` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.mem_subdomain_of_eq_vals` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:818](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L818) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.mem_subdomain_of_eq_vals` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1376](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1376) — (no docstring)
- `lemma Domain.CosetFftDomainClass.mem_subdomain_of_eq_vals` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:109](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L109) — (no docstring)

### `mem_toFinset_iff_mem` (3 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:71](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L71) — (no docstring)
- `lemma Domain.CosetFftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:112](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L112) — (no docstring)
- `lemma Domain.FftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/FftDomain/Mem.lean:69](../../../ArkLib/Data/Domain/FftDomain/Mem.lean#L69) — (no docstring)

### `neg_mem_domain_iff_mem` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.neg_mem_domain_iff_mem` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:460](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L460) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.neg_mem_domain_iff_mem` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1308](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1308) — (no docstring)
- `lemma Domain.CosetFftDomainClass.neg_mem_domain_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:90](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L90) — (no docstring)

### `neg_mem_domain_of_mem` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.neg_mem_domain_of_mem` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:452](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L452) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.neg_mem_domain_of_mem` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1297](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1297) — (no docstring)
- `theorem Domain.CosetFftDomainClass.neg_mem_domain_of_mem` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:83](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L83) — (no docstring)

### `rdrop` (3 declarations, 2 files)

- `abbrev Fin.rdrop` [ArkLib/Data/Fin/Tuple/Defs.lean:68](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L68) — Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. This is defi
- `def ProtocolSpec.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:131](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L131) — Drop the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:188](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L188) — (no docstring)

### `reduction_perfectCompleteness` (3 declarations, 2 files)

- `theorem DoNothing.reduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:51](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L51) — The `DoNothing` reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:742](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L742) — Perfect completeness for the (non-oracle) reduction
- `theorem Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1775](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1775) — (no docstring)

### `rtake` (3 declarations, 2 files)

- `def Fin.rtake` [ArkLib/Data/Fin/Tuple/Defs.lean:55](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L55) — Take the last `m` elements of a finite vector
- `def ProtocolSpec.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:123](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L123) — Take the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:180](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L180) — Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec`

### `toList_eq_finset_toList` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.toList_eq_finset_toList` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:291](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L291) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.toList_eq_finset_toList` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:619](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L619) — (no docstring)
- `lemma Domain.CosetFftDomainClass.toList_eq_finset_toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:41](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L41) — (no docstring)

### `toSubgroup` (3 declarations, 2 files)

- `def ReedSolomon.FftDomain.toSubgroup` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:296](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L296) — (no docstring)
- `def Domain.FftDomainClass.toSubgroup` [ArkLib/Data/Domain/FftDomain/ToSubgroup.lean:36](../../../ArkLib/Data/Domain/FftDomain/ToSubgroup.lean#L36) — (no docstring)
- `abbrev Domain.FftDomain.toSubgroup` [ArkLib/Data/Domain/FftDomain/ToSubgroup.lean:77](../../../ArkLib/Data/Domain/FftDomain/ToSubgroup.lean#L77) — (no docstring)

### `twoNthRoot` (3 declarations, 2 files)

- `def ReedSolomon.FftDomain.twoNthRoot` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1258](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1258) — Finds a `2 ^ n`th root of `x`.
- `def ReedSolomon.CosetFftDomain.twoNthRoot` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1909](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1909) — Finds a `2 ^ n`th root of `x`.
- `def Domain.CosetFftDomain.twoNthRoot` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:442](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L442) — Finds a `2 ^ n`th root of `x`.

### `twoNthRootAux` (3 declarations, 2 files)

- `def ReedSolomon.FftDomain.twoNthRootAux` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1246](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1246) — (no docstring)
- `def ReedSolomon.CosetFftDomain.twoNthRootAux` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1897](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1897) — (no docstring)
- `def Domain.CosetFftDomain.twoNthRootAux` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:430](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L430) — (no docstring)

### `twoNthRootAux_correct` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.twoNthRootAux_correct` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1262](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1262) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.twoNthRootAux_correct` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1913](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1913) — (no docstring)
- `lemma Domain.CosetFftDomain.twoNthRootAux_correct` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:446](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L446) — (no docstring)

### `twoNthRoot_correct` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.twoNthRoot_correct` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1274](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1274) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.twoNthRoot_correct` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1925](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1925) — (no docstring)
- `lemma Domain.CosetFftDomain.twoNthRoot_correct` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:460](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L460) — (no docstring)

### `AbstractOStmtIn` (2 declarations, 2 files)

- `structure Binius.RingSwitching.AbstractOStmtIn` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:241](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L241) — (no docstring)
- `structure RingSwitching.AbstractOStmtIn` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:251](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L251) — (no docstring)

### `AbstractOStmtIn.toRelInput` (2 declarations, 2 files)

- `def Binius.RingSwitching.AbstractOStmtIn.toRelInput` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:249](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L249) — (no docstring)
- `def RingSwitching.AbstractOStmtIn.toRelInput` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:259](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L259) — (no docstring)

### `BatchingStmtIn` (2 declarations, 2 files)

- `structure Binius.RingSwitching.BatchingStmtIn` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:216](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L216) — (no docstring)
- `structure RingSwitching.BatchingStmtIn` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:220](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L220) — (no docstring)

### `BatchingWitIn` (2 declarations, 2 files)

- `structure Binius.RingSwitching.BatchingWitIn` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:212](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L212) — (no docstring)
- `structure RingSwitching.BatchingWitIn` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:216](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L216) — (no docstring)

### `BindingAdversary` (2 declarations, 2 files)

- `structure Commitment.BindingAdversary` [ArkLib/CommitmentScheme/Basic.lean:116](../../../ArkLib/CommitmentScheme/Basic.lean#L116) — An adversary in the (evaluation) binding game returns a commitment `cm`, a query `q`, two purported 
- `structure CommitmentScheme.BindingAdversary` [ArkLib/CommitmentScheme/CommitmentScheme.lean:89](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L89) — An adversary in the binding game returns a commitment and two purported openings to possibly differe

### `ChallengeIdx` (2 declarations, 2 files)

- `def ProtocolSpec.ChallengeIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:64](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L64) — Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification
- `def ProtocolSpec.VectorSpec.ChallengeIdx` [ArkLib/OracleReduction/VectorIOR.lean:54](../../../ArkLib/OracleReduction/VectorIOR.lean#L54) — The type of indices for challenges in a `VectorSpec`.

### `Codec` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.Codec` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:202](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L202) — Paper-facing alias for CO25 Definition 4.1 codecs.
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

### `CosetFftDomain` (2 declarations, 2 files)

- `structure ReedSolomon.CosetFftDomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:507](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L507) — A coset FFT domain is a domain of the form `x · G` for an FFT domain `G`.
- `structure Domain.CosetFftDomain` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:37](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L37) — A coset FFT domain is a domain of the form `x · G` for an FFT domain `G`.

### `CurveCoeffPolys` (2 declarations, 2 files)

- `def ArkLib.BetaToCurveCoeffPolys.CurveCoeffPolys` [ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean:96](../../../ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean#L96) — Asserts that each coefficient of the decoded polynomial $P(z)$ at index $j < deg$ is interpolated by
- `def ArkLib.KeystoneCapstone.CurveCoeffPolys` [ArkLib/ToMathlib/KeystoneCapstone.lean:90](../../../ArkLib/ToMathlib/KeystoneCapstone.lean#L90) — (no docstring)

### `ExtractabilityAdversary` (2 declarations, 2 files)

- `abbrev Commitment.ExtractabilityAdversary` [ArkLib/CommitmentScheme/Basic.lean:183](../../../ArkLib/CommitmentScheme/Basic.lean#L183) — An adversary in the extractability game is an oracle computation that returns a commitment, a query,
- `structure CommitmentScheme.ExtractabilityAdversary` [ArkLib/CommitmentScheme/CommitmentScheme.lean:137](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L137) — An adversary in the extractability game returns a commitment, a claimed message/opening pair, and au

### `FftDomain` (2 declarations, 2 files)

- `structure ReedSolomon.FftDomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:142](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L142) — An FFT domain is an injective group homomorphism whose codomain is the multiplicative group of a fie
- `structure Domain.FftDomain` [ArkLib/Data/Domain/FftDomain/Defs.lean:34](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L34) — (no docstring)

### `FinalSumcheckWit` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:1618](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L1618) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1292](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1292) — (no docstring)

### `GenMutualCorrParams` (2 declarations, 2 files)

- `class Fold.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/Folding.lean:681](../../../ArkLib/ProofSystem/Whir/Folding.lean#L681) — The `GenMutualCorrParams` class captures the necessary parameters and assumptions to model a sequenc
- `class WhirIOP.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:85](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L85) — `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes `C_{i : M + 1, j : foldingPar

### `KeyGen` (2 declarations, 2 files)

- `structure Commitment.KeyGen` [ArkLib/CommitmentScheme/Basic.lean:49](../../../ArkLib/CommitmentScheme/Basic.lean#L49) — Key generation for a commitment scheme, producing a committer key and a verifier key.
- `structure CommitmentScheme.KeyGen` [ArkLib/CommitmentScheme/CommitmentScheme.lean:34](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L34) — The key-generation algorithm, returning separate keys for the committer and verifier.

### `MLIOPCS` (2 declarations, 2 files)

- `structure Binius.RingSwitching.MLIOPCS` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:255](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L255) — (no docstring)
- `structure RingSwitching.MLIOPCS` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:265](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L265) — (no docstring)

### `MLIOPCSStmt` (2 declarations, 2 files)

- `structure Binius.RingSwitching.MLIOPCSStmt` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:231](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L231) — (no docstring)
- `structure RingSwitching.MLIOPCSStmt` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:241](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L241) — (no docstring)

### `MLPEvalRelation` (2 declarations, 2 files)

- `def Binius.RingSwitching.MLPEvalRelation` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:236](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L236) — Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation
- `def RingSwitching.MLPEvalRelation` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:246](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L246) — Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation

### `MLPEvalStatement` (2 declarations, 2 files)

- `structure Binius.RingSwitching.MLPEvalStatement` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:203](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L203) — Initial input (input to the batching phase): a polynomial-evaluation claim `s = t(r)`.
- `structure RingSwitching.MLPEvalStatement` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:207](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L207) — Initial input (input to the Batching Phase): a polynomial-evaluation claim `s = t(r)`.

### `MessageIdx` (2 declarations, 2 files)

- `def ProtocolSpec.MessageIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:59](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L59) — Subtype of `Fin n` for the indices corresponding to messages in a protocol specification
- `def ProtocolSpec.VectorSpec.MessageIdx` [ArkLib/OracleReduction/VectorIOR.lean:50](../../../ArkLib/OracleReduction/VectorIOR.lean#L50) — The type of indices for messages in a `VectorSpec`.

### `OracleProver` (2 declarations, 2 files)

- `abbrev Interaction.OracleDecoration.OracleProver` [ArkLib/Interaction/Oracle/Core.lean:889](../../../ArkLib/Interaction/Oracle/Core.lean#L889) — Oracle prover: given ambient input `i`, local statement/oracle data, performs monadic setup in `Orac
- `def OracleProver` [ArkLib/OracleReduction/Basic.lean:446](../../../ArkLib/OracleReduction/Basic.lean#L446) — An **(oracle) prover** in an interactive **oracle** reduction is a prover in the non-oracle reductio

### `OracleReduction` (2 declarations, 2 files)

- `structure Interaction.OracleDecoration.OracleReduction` [ArkLib/Interaction/Oracle/Core.lean:919](../../../ArkLib/Interaction/Oracle/Core.lean#L919) — Oracle reduction: pairs an oracle prover with a verifier that uses per-node monads (`Id` at sender, 
- `structure OracleReduction` [ArkLib/OracleReduction/Basic.lean:647](../../../ArkLib/OracleReduction/Basic.lean#L647) — An **interactive oracle reduction** for a given protocol specification `pSpec`, and relative to orac

### `OracleVerifier` (3 declarations, 2 files)

- `structure Interaction.OracleVerifier` [ArkLib/Interaction/Oracle/Core.lean:1033](../../../ArkLib/Interaction/Oracle/Core.lean#L1033) — A verifier-only oracle protocol surface, analogous to `Interaction.Verifier`. Its primary index is t
- `structure OracleVerifier` [ArkLib/OracleReduction/Basic.lean:175](../../../ArkLib/OracleReduction/Basic.lean#L175) — (no docstring)
- `structure OracleVerifier` [ArkLib/OracleReduction/Basic.lean:466](../../../ArkLib/OracleReduction/Basic.lean#L466) — An **(oracle) verifier** of an interactive **oracle** reduction consists of: - an oracle computation

### `OutputOracleStatement` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:106](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L106) — Output oracle statement: the IOR has no output oracle component.
- `def ToyProblem.SimplifiedIOR.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:77](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L77) — Output oracle statement: the single combined codeword `f_new := f₁ + γ·f₂ : ι → F`.

### `OutputWitness` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:110](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L110) — Output witness: empty.
- `def ToyProblem.SimplifiedIOR.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:81](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L81) — Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`.

### `ParamConditions` (2 declarations, 2 files)

- `structure StirIOP.ParamConditions` [ArkLib/ProofSystem/Stir/MainThm.lean:55](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L55) — **Conditions that protocol parameters must satisfy.** - `h_deg` : initial degree `deg` is a power of
- `structure WhirIOP.ParamConditions` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:66](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L66) — ** Conditions that protocol parameters must satisfy. ** h_m : m = varCount₀ h_sumkLt : ∑ i : Fin (M 

### `Proof` (2 declarations, 2 files)

- `abbrev Interaction.Proof` [ArkLib/Interaction/Reduction.lean:216](../../../ArkLib/Interaction/Reduction.lean#L216) — A proof system is a reduction where the prover does not forward any witness to the next stage (`Witn
- `def Proof` [ArkLib/OracleReduction/Basic.lean:671](../../../ArkLib/OracleReduction/Basic.lean#L671) — An **interactive proof (IP)** is an interactive reduction where the output statement is a boolean, t

### `PrvState` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.PrvState` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:319](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L319) — The state maintained by the prover throughout the batching phase.
- `def RingSwitching.BatchingPhase.PrvState` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:121](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L121) — The state maintained by the prover throughout the batching phase.

### `RewindingExtractor` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.RewindingExtractor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:153](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L153) — Paper-facing alias for the rewinding extractor interface from CO25 Definition 3.8.
- `def Extractor.RewindingExtractor` [ArkLib/ToMathlib/RewindingExtractor.lean:115](../../../ArkLib/ToMathlib/RewindingExtractor.lean#L115) — A **rewinding extractor** for the 2-special-sound case: given the recorded prefix and **two** comple

### `RingSwitchingBaseContext` (2 declarations, 2 files)

- `structure Binius.RingSwitching.RingSwitchingBaseContext` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:220](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L220) — (no docstring)
- `structure RingSwitching.RingSwitchingBaseContext` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:224](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L224) — (no docstring)

### `RingSwitching_SumcheckMultParam` (2 declarations, 2 files)

- `def Binius.RingSwitching.RingSwitching_SumcheckMultParam` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:381](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L381) — Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier.
- `def RingSwitching.RingSwitching_SumcheckMultParam` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:388](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L388) — Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier.

### `Scheme` (2 declarations, 2 files)

- `structure Commitment.Scheme` [ArkLib/CommitmentScheme/Basic.lean:64](../../../ArkLib/CommitmentScheme/Basic.lean#L64) — A commitment scheme with key generation, commitment, and opening algorithms.
- `structure CommitmentScheme.Scheme` [ArkLib/CommitmentScheme/CommitmentScheme.lean:46](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L46) — An ordinary commitment scheme.

### `SmoothCosetFftDomain` (2 declarations, 2 files)

- `abbrev ReedSolomon.SmoothCosetFftDomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:722](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L722) — A smooth coset FFT domain is a coset FFT domain whose underlying FFT domain is smooth.
- `abbrev Domain.SmoothCosetFftDomain` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:238](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L238) — (no docstring)

### `SmoothFftDomain` (2 declarations, 2 files)

- `abbrev ReedSolomon.SmoothFftDomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:413](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L413) — A smooth FFT domain is an FFT domain whose domain (i.e. LHS) is a finite additive cyclic group, whic
- `abbrev Domain.SmoothFftDomain` [ArkLib/Data/Domain/FftDomain/Defs.lean:121](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L121) — (no docstring)

### `SpongeState` (2 declarations, 2 files)

- `class SpongeState` [ArkLib/Data/Hash/DuplexSponge.lean:255](../../../ArkLib/Data/Hash/DuplexSponge.lean#L255) — Type class for the state of a cryptographic permutation used in the duplex sponge construction. Rust
- `abbrev DuplexSpongeFS.SpongeState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:40](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L40) — Paper-facing alias for the canonical duplex-sponge state used in CO25 Section 3.3.

### `SumcheckMultiplierParam` (2 declarations, 2 files)

- `structure Sumcheck.Structured.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured.lean:85](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L85) — Parameters describing how the round polynomial `H` is built from the witness `t`: `H = P · Q(t)`, wh
- `structure Sumcheck.Structured.Prismalinear.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:50](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L50) — Parameters describing how a *prismalinear* round polynomial `H = P · Q(t)` is built from the witness

### `TensorAlgebra` (2 declarations, 2 files)

- `abbrev Binius.RingSwitching.TensorAlgebra` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:63](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L63) — Tensor Algebra A = L ⊗_K L. Based on the spec, it's viewed as (2^κ)x(2^κ) arrays of K-elements. The 
- `abbrev RingSwitching.TensorAlgebra` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:62](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L62) — Tensor Algebra A = L ⊗_K L. Based on the spec, it's viewed as (2^κ)x(2^κ) arrays of K-elements. The 

### `Verifier.run` (2 declarations, 2 files)

- `def Interaction.Verifier.run` [ArkLib/Interaction/Reduction.lean:246](../../../ArkLib/Interaction/Reduction.lean#L246) — Run a prover strategy against a verifier. Convenience wrapper around `Spec.Strategy.runWithRoles` th
- `def Verifier.run` [ArkLib/OracleReduction/Execution.lean:186](../../../ArkLib/OracleReduction/Execution.lean#L186) — Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and the t

### `WitIn` (2 declarations, 2 files)

- `def RandomQuery.WitIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:36](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L36) — (no docstring)
- `def Logup.WitIn` [ArkLib/ProofSystem/Logup/Common.lean:367](../../../ArkLib/ProofSystem/Logup/Common.lean#L367) — Protocol 2 has no private witness beyond the input oracles at this layer.

### `WitMLP` (2 declarations, 2 files)

- `structure Binius.RingSwitching.WitMLP` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:209](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L209) — (no docstring)
- `structure RingSwitching.WitMLP` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:213](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L213) — (no docstring)

### `aeval_eqPolynomial_zeroOne` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.aeval_eqPolynomial_zeroOne` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:683](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L683) — `aeval` of `eqPolynomial` at a Boolean coefficient vector lands in `L₀` as `eqTilde`.
- `lemma RingSwitching.aeval_eqPolynomial_zeroOne` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:773](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L773) — `aeval` of `eqPolynomial` at a Boolean coefficient vector lands in `L₀` as `eqTilde`.

### `aeval_eq_sum_eqTilde` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.aeval_eq_sum_eqTilde` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:700](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L700) — **MLE evaluation identity (through the algebra map).** For a multilinear `t` over `K₀`, its `L₀`-eva
- `lemma RingSwitching.aeval_eq_sum_eqTilde` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:790](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L790) — **MLE evaluation identity (through the algebra map).** For a multilinear `t` over `K₀`, its `L₀`-eva

### `agree` (2 declarations, 2 files)

- `def CodeGeometry.agree` [ArkLib/Data/CodingTheory/CodeGeometry.lean:35](../../../ArkLib/Data/CodingTheory/CodeGeometry.lean#L35) — (no docstring)
- `def ProximityGap.WeightedAgreement.agree` [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean:179](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean#L179) — Relative `μ`-agreement between words `u` and `v`.

### `answer_instDefault` (2 declarations, 2 files)

- `lemma RingSwitching.BatchingPhase.answer_instDefault` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:54](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L54) — The default oracle interface (`OracleInterface.instDefault`, used by the ring-switching message orac
- `lemma ToyProblem.Spec.answer_instDefault` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:614](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L614) — `answer` of the default oracle interface is the identity (the message itself).

### `append_left_injective` (2 declarations, 2 files)

- `theorem Fin.append_left_injective` [ArkLib/Data/Fin/Basic.lean:262](../../../ArkLib/Data/Fin/Basic.lean#L262) — (no docstring)
- `theorem ProtocolSpec.append_left_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:65](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L65) — (no docstring)

### `append_right_injective` (2 declarations, 2 files)

- `theorem Fin.append_right_injective` [ArkLib/Data/Fin/Basic.lean:270](../../../ArkLib/Data/Fin/Basic.lean#L270) — (no docstring)
- `theorem ProtocolSpec.append_right_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:75](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L75) — (no docstring)

### `batchingCore_perfectCompleteness` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.FullRingSwitching.batchingCore_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:110](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L110) — (no docstring)
- `lemma RingSwitching.FullRingSwitching.batchingCore_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/General.lean:121](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L121) — (no docstring)

### `batchingInputRelation` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingInputRelation` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:97](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L97) — Input relation: the witness `t` and `t'` are consistent, and `t` satisfies the original claim.
- `def RingSwitching.BatchingPhase.batchingInputRelation` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:300](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L300) — Input relation: the witness `t` and `t'` are consistent, and `t` satisfies the original claim.

### `batchingInputRelationProp` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingInputRelationProp` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:85](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L85) — (no docstring)
- `def RingSwitching.BatchingPhase.batchingInputRelationProp` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:293](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L293) — (no docstring)

### `batchingKStateProp` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingKStateProp` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:434](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L434) — (no docstring)
- `def RingSwitching.BatchingPhase.batchingKStateProp` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:334](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L334) — (no docstring)

### `batchingKnowledgeStateFunction` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:482](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L482) — Knowledge state function for the batching phase.
- `def RingSwitching.BatchingPhase.batchingKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:404](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L404) — Knowledge state function for the batching phase.

### `batchingOracleReduction` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:394](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L394) — The Oracle Reduction for the Batching Phase.
- `def RingSwitching.BatchingPhase.batchingOracleReduction` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:273](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L273) — The Oracle Reduction for the Batching Phase.

### `batchingOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:1219](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L1219) — RBR knowledge soundness for the batching phase oracle verifier.
- `theorem RingSwitching.BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:548](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L548) — RBR knowledge soundness for the batching phase oracle verifier. `IsDomain K` (alongside the existing

### `batchingRBRKnowledgeError` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingRBRKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:432](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L432) — RBR knowledge soundness error for the batching phase. The only verifier randomness is `r''`. A colli
- `def RingSwitching.BatchingPhase.batchingRBRKnowledgeError` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:329](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L329) — RBR knowledge soundness error for the batching phase. The only verifier randomness is `r''`. A colli

### `batchingRbrExtractor` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingRbrExtractor` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:414](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L414) — RBR extractor for the batching phase.
- `def RingSwitching.BatchingPhase.batchingRbrExtractor` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:311](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L311) — RBR extractor for the batching phase.

### `batchingReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.BatchingPhase.batchingReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:648](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L648) — Perfect completeness for the batching phase oracle reduction. This theorem proves that the honest pr
- `theorem RingSwitching.BatchingPhase.batchingReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:534](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L534) — Batching completeness from the explicit local algebraic residual.

### `batchingWitMid` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingWitMid` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:408](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L408) — Intermediate witness types for RBR knowledge soundness.
- `def RingSwitching.BatchingPhase.batchingWitMid` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:305](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L305) — Intermediate witness types for RBR knowledge soundness.

### `binomial_separation` (2 declarations, 2 files)

- `theorem ProximityGap.MultiplicativeRigidity.binomial_separation` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean:154](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean#L154) — **Binomial separation.** If `0 < b < a ≤ k`, then two distinct monomials `c₁ * X ^ a` and `c₂ * X ^ 
- `theorem MultiplicativeRigidity.binomial_separation` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean:171](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean#L171) — **Binomial separation.** Packaging of coset rigidity in the form the dossier consumes: if `b < a < k

### `boolHypercubeEmb` (2 declarations, 2 files)

- `def Binius.RingSwitching.boolHypercubeEmb` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:889](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L889) — The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → L₀)` induced by a 2-element domain embed
- `def RingSwitching.boolHypercubeEmb` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1349](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1349) — The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → L₀)` induced by a 2-element domain embed

### `boolHypercube_sum_eq` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.boolHypercube_sum_eq` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:897](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L897) — **`𝓑`-domain hypercube sum reindexes to the Boolean hypercube.** For any `𝓑 : Fin 2 ↪ L₀`, summing `
- `lemma RingSwitching.boolHypercube_sum_eq` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1357](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1357) — **`𝓑`-domain hypercube sum reindexes to the Boolean hypercube.** For any `𝓑 : Fin 2 ↪ L₀`, summing `

### `boolHypercube_sum_pinned` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.boolHypercube_sum_pinned` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:917](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L917) — **Pinned-`𝓑` Boolean-domain sumcheck sum.** When `𝓑` is pinned to the Boolean embedding (`𝓑 c = if c
- `lemma RingSwitching.boolHypercube_sum_pinned` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1377](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1377) — **Pinned-`𝓑` Boolean-domain sumcheck sum.** When `𝓑` is pinned to the Boolean embedding (`𝓑 c = if c

### `c0_ne_c1` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c0_ne_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:36](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L36) — The three codewords are pairwise distinct.
- `theorem JohnsonBound.JqlRefutation.c0_ne_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:75](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L75) — The three codewords are pairwise distinct.

### `c0_ne_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c0_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:37](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L37) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.c0_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:76](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L76) — (no docstring)

### `c1_ne_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c1_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:38](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L38) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.c1_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:77](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L77) — (no docstring)

### `check_rows_sum_eq_aeval` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.check_rows_sum_eq_aeval` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:740](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L740) — **DP24 ring-switching capstone (sum form).** The verifier's row-decomposition check sum, applied to 
- `lemma RingSwitching.check_rows_sum_eq_aeval` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1207](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1207) — **DP24 ring-switching capstone (sum form).** The verifier's row-decomposition check sum, applied to 

### `coeffHom_apply` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom_apply` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:180](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L180) — (no docstring)
- `theorem CompPoly.CPolynomial.coeffHom_apply` [ArkLib/ToCompPoly/Univariate/Basic.lean:290](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L290) — (no docstring)

### `coeff_S_eq_zero_of_lt` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_eq_zero_of_lt` [ArkLib/Data/Polynomial/HenselExistence.lean:202](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L202) — The `t`-th partial sum is supported on `[0, t]`: every coefficient above order `t` vanishes. (`S t` 
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_eq_zero_of_lt` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:279](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L279) — `S t` is supported on `[0, t]`: every coefficient above order `t` vanishes.

### `coeff_S_stable` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_stable` [ArkLib/Data/Polynomial/HenselExistence.lean:213](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L213) — Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`. The diagonal value is reached a
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_stable` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:289](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L289) — Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`.

### `coeff_S_succ_of_le` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_succ_of_le` [ArkLib/Data/Polynomial/HenselExistence.lean:196](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L196) — Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_succ_of_le` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:274](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L274) — Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.

### `coeff_aeval_eq_sum_range` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_aeval_eq_sum_range` [ArkLib/Data/Polynomial/HenselExistence.lean:64](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L64) — Local copy of `NewtonLinearization.coeff_aeval_eq_sum_range`: `coeff n (aeval γ P) = ∑_{i ≤ deg P} P
- `theorem ProximityPrize.NewtonLinearization.coeff_aeval_eq_sum_range` [ArkLib/Data/Polynomial/NewtonLinearization.lean:165](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L165) — Local restatement of the `HasSubst`-free `aeval`-coefficient expansion (this is `ProximityPrize.coef

### `coeff_aeval_sub_at` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_aeval_sub_at` [ArkLib/Data/Polynomial/HenselExistence.lean:146](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L146) — Local copy of `NewtonLinearization.coeff_aeval_sub_at` (the `P'(c)`-linear response). For `P : R[X]`
- `theorem ProximityPrize.NewtonLinearization.coeff_aeval_sub_at` [ArkLib/Data/Polynomial/NewtonLinearization.lean:185](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L185) — **Newton/Hensel linearization of the composed series (P2 form).** For a polynomial `P` over `R` and 

### `coeff_γ` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_γ` [ArkLib/Data/Polynomial/HenselExistence.lean:226](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L226) — (no docstring)
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_γ` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:302](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L302) — (no docstring)

### `coeff_γ_eq_S` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_γ_eq_S` [ArkLib/Data/Polynomial/HenselExistence.lean:235](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L235) — `γ` agrees with the `t`-th partial sum below order `t + 1`.
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_γ_eq_S` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:311](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L311) — `γ` agrees with the `t`-th partial sum below order `t + 1`.

### `coeffs` (2 declarations, 2 files)

- `def Polynomial.Bivariate.coeffs` [ArkLib/Data/Polynomial/Bivariate.lean:34](../../../ArkLib/Data/Polynomial/Bivariate.lean#L34) — The set of coefficients of a bivariate polynomial.
- `def UniPoly.coeffs` [ArkLib/Data/UniPoly/Basic.lean:41](../../../ArkLib/Data/UniPoly/Basic.lean#L41) — (no docstring)

### `componentWise_φ₁_embed_MLE` (2 declarations, 2 files)

- `def Binius.RingSwitching.componentWise_φ₁_embed_MLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:171](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L171) — **Component-wise `φ₁` embedding**. Takes a polynomial `t'` with coefficients in `L` and embeds it in
- `def RingSwitching.componentWise_φ₁_embed_MLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:192](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L192) — Binius-named alias: component-wise `φ₁` embedding into the tensor algebra `L ⊗[K] L`.

### `computeRoundPoly` (2 declarations, 2 files)

- `def Sumcheck.Structured.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured.lean:130](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L130) — The general round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` is the public multilinea
- `def Sumcheck.Structured.Prismalinear.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:70](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L70) — The *prismalinear* round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` has per-variable 

### `compute_A_MLE` (2 declarations, 2 files)

- `def Binius.RingSwitching.compute_A_MLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:370](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L370) — Step 4b: P writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension of `A_func`.
- `def RingSwitching.compute_A_MLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:377](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L377) — Step 4b: P writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension of `A_func`.

### `compute_A_func` (2 declarations, 2 files)

- `def Binius.RingSwitching.compute_A_func` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:353](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L353) — Step 4a: For each `w ∈ {0,1}^{ℓ'}`, P decompose `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})` `=: Σ_{
- `def RingSwitching.compute_A_func` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:360](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L360) — Step 4a: For each `w ∈ {0,1}^{ℓ'}`, P decompose `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})` `=: Σ_{

### `compute_final_eq_tensor` (2 declarations, 2 files)

- `def Binius.RingSwitching.compute_final_eq_tensor` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:401](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L401) — Compute the tensor `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))`
- `def RingSwitching.compute_final_eq_tensor` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:409](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L409) — Compute the tensor `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))`

### `compute_final_eq_value` (2 declarations, 2 files)

- `def Binius.RingSwitching.compute_final_eq_value` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:411](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L411) — Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`, where e_u is the row compone
- `def RingSwitching.compute_final_eq_value` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:419](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L419) — Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`, where e_u is the row compone

### `compute_s0` (2 declarations, 2 files)

- `def Binius.RingSwitching.compute_s0` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:394](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L394) — Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`, where ŝ_u is the row components o
- `def RingSwitching.compute_s0` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:402](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L402) — Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`, where ŝ_u is the row components o

### `constantCoeff_γ` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.constantCoeff_γ` [ArkLib/Data/Polynomial/HenselExistence.lean:230](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L230) — The constant coefficient of the Newton root is the prescribed root `c`.
- `theorem ProximityPrize.HenselSeriesCoeff.constantCoeff_γ` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:306](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L306) — The constant coefficient of the Newton root is the prescribed root `c`.

### `coreInteractionOracleRbrKnowledgeError` (2 declarations, 2 files)

- `def coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1138](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1138) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1698](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1698) — (no docstring)

### `coreInteractionOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1110](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1110) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1658](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1658) — Perfect completeness for the core interaction oracle reduction

### `coreInteractionOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1146](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1146) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1707](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1707) — Round-by-round knowledge soundness for the core interaction oracle verifier

### `coreInteractionRbrKnowledgeError` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.coreInteractionRbrKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1766](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1766) — standard sumcheck error
- `def RingSwitching.SumcheckPhase.coreInteractionRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1298](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1298) — standard sumcheck error

### `coreInteraction_perfectCompleteness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.SumcheckPhase.coreInteraction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1725](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1725) — Perfect completeness for large-field reduction (Sumcheck ++ FinalSum)
- `theorem RingSwitching.SumcheckPhase.coreInteraction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1252](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1252) — Perfect completeness for large-field reduction (Sumcheck ++ FinalSum), conditional on the explicit i

### `coreInteraction_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1799](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1799) — RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum)
- `theorem RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1309](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1309) — RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum)

### `decoder` (2 declarations, 2 files)

- `def BerlekampWelch.decoder` [ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:52](../../../ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean#L52) — Berlekamp-Welch decoder for Reed-Solomon codes. Given received codeword evaluations with potential e
- `def GuruswamiSudan.decoder` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:113](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L113) — Specification-level Guruswami-Sudan decoder. This finite-field specification enumerates all degree-`

### `decompose_rows_packMLE` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.decompose_rows_packMLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:598](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L598) — **Row recovery of `t`-evaluations.** The row components of the prover's tensor `ŝ = embedded_MLP_eva
- `lemma RingSwitching.decompose_rows_packMLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1186](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1186) — **Row recovery of `t`-evaluations.** The row components of the prover's tensor `ŝ = embedded_MLP_eva

### `decompose_rows_sum` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.decompose_rows_sum` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:552](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L552) — `decompose_tensor_algebra_rows` is additive over finite sums of tensors.
- `lemma RingSwitching.decompose_rows_sum` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:668](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L668) — `decompose_tensor_algebra_rows` is additive over finite sums of tensors.

### `decompose_rows_φ₀φ₁` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.decompose_rows_φ₀φ₁` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:562](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L562) — Row decomposition of a separated tensor `φ₀(a) · φ₁(b) = a ⊗ b`: the `u`-th row component represents
- `lemma RingSwitching.decompose_rows_φ₀φ₁` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:678](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L678) — Row decomposition of a separated tensor `φ₀(a) · φ₁(b) = a ⊗ b`: the `u`-th row component represents

### `decompose_tensor_algebra_columns` (2 declarations, 2 files)

- `def Binius.RingSwitching.decompose_tensor_algebra_columns` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:100](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L100) — Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v)`. This views `L ⊗ L` as a mod
- `def RingSwitching.decompose_tensor_algebra_columns` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:99](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L99) — Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v)`. This views `L ⊗ L` as a mod

### `decompose_tensor_algebra_rows` (2 declarations, 2 files)

- `def Binius.RingSwitching.decompose_tensor_algebra_rows` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:92](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L92) — Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u)`. This views `L ⊗ L` as a module
- `def RingSwitching.decompose_tensor_algebra_rows` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:91](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L91) — Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u)`. This views `L ⊗ L` as a module

### `degree` (2 declarations, 2 files)

- `def UniPoly.degree` [ArkLib/Data/UniPoly/Basic.lean:66](../../../ArkLib/Data/UniPoly/Basic.lean#L66) — Return the degree of a `UniPoly`.
- `def StirIOP.degree` [ArkLib/ProofSystem/Stir/MainThm.lean:45](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L45) — **Degree after `i` folds:** The starting degree is `deg`; every fold divides it by `foldingParamⱼ (j

### `domain_implies_char_ne_2` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:98](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L98) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:134](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L134) — (no docstring)

### `domain_sub_eq_div_domain` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.domain_sub_eq_div_domain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:395](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L395) — (no docstring)
- `lemma Domain.FftDomainClass.domain_sub_eq_div_domain` [ArkLib/Data/Domain/FftDomain/Ops.lean:61](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L61) — (no docstring)

### `duplexSpongeTraceEntry` (2 declarations, 2 files)

- `abbrev OracleSpec.duplexSpongeTraceEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:370](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L370) — The type of a single entry in a duplex sponge query trace. Implicit-parameter companion to `DSTraceS
- `abbrev DuplexSpongeFS.DSTraceStorage.duplexSpongeTraceEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean:47](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean#L47) — A single query-answer entry of a `DuplexSpongeTrace`, i.e. one element of the underlying `QueryLog` 

### `embedded_MLP_eval` (2 declarations, 2 files)

- `def Binius.RingSwitching.embedded_MLP_eval` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:320](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L320) — Compute the tensor value ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))
- `def RingSwitching.embedded_MLP_eval` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:328](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L328) — Compute the tensor value ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))

### `embedded_MLP_eval_eq_sum` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.embedded_MLP_eval_eq_sum` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:523](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L523) — **DP24 packing expansion.** The prover's tensor `ŝ := φ₁(t')(φ₀(r_κ), …, φ₀(r_{ℓ-1}))` expands over 
- `lemma RingSwitching.embedded_MLP_eval_eq_sum` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1150](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1150) — **DP24 packing expansion.** The prover's tensor `ŝ := φ₁(t')(φ₀(r_κ), …, φ₀(r_{ℓ-1}))` expands over 

### `empty` (2 declarations, 2 files)

- `def DuplexSpongeFS.DSTraceStorage.ListBacked.empty` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean:529](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean#L529) — (no docstring)
- `def ProtocolSpec.empty` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:53](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L53) — The empty protocol specification, with no messages or challenges, written as `!p[]`.

### `eqPoly_collapse` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.eqPoly_collapse` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:508](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L508) — The full `eqPolynomial` collapses through the mixed embedding to `φ₀` of its ordinary evaluation, by
- `lemma RingSwitching.eqPoly_collapse` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:655](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L655) — The full `eqPolynomial` collapses through the mixed embedding to `φ₀` of its ordinary evaluation, by

### `eqTilde_concat_split` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.eqTilde_concat_split` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:665](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L665) — `eqTilde` of concatenated Boolean / point data factors along the κ/ℓ' split: `eqTilde (concat fp fs)
- `lemma RingSwitching.eqTilde_concat_split` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:756](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L756) — `eqTilde` of concatenated Boolean / point data factors along the κ/ℓ' split: `eqTilde (concat fp fs)

### `eqTilde_prod` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.eqTilde_prod` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:616](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L616) — `eqTilde` written as a product over coordinates of the symmetric Boolean factor.
- `lemma RingSwitching.eqTilde_prod` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:708](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L708) — `eqTilde` written as a product over coordinates of the symmetric Boolean factor.

### `eq_iff_domains_eq` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.eq_iff_domains_eq` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:150](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L150) — (no docstring)
- `lemma Domain.FftDomain.eq_iff_domains_eq` [ArkLib/Data/Domain/FftDomain/Defs.lean:41](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L41) — (no docstring)

### `eq_iff_generators_eq` (2 declarations, 2 files)

- `theorem ReedSolomon.FftDomain.eq_iff_generators_eq` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:497](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L497) — (no docstring)
- `theorem Domain.FftDomainClass.eq_iff_generators_eq` [ArkLib/Data/Domain/FftDomain/Ops.lean:128](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L128) — (no docstring)

### `eval` (2 declarations, 2 files)

- `def UniPoly.eval` [ArkLib/Data/UniPoly/Basic.lean:412](../../../ArkLib/Data/UniPoly/Basic.lean#L412) — Evaluates a `UniPoly` at a given value
- `def Plonk.Gate.eval` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:54](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L54) — Evaluate a gate on a given input vector.

### `eval_fft_domain_eq_eval_domain` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.eval_fft_domain_eq_eval_domain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:166](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L166) — (no docstring)
- `lemma Domain.FftDomain.eval_fft_domain_eq_eval_domain` [ArkLib/Data/Domain/FftDomain/Defs.lean:61](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L61) — (no docstring)

### `exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` (2 declarations, 2 files)

- `lemma ProximityGap.exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6648](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6648) — Complement-to-incidence form of the heavy-coordinate argument.  If a coordinate is not heavy for the
- `lemma ArkLib.Claim511.exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` [ArkLib/ToMathlib/Claim511.lean:129](../../../ArkLib/ToMathlib/Claim511.lean#L129) — **Complement-to-incidence selection.** If at least `r` coordinates are *not* heavy (each bad for `< 

### `exists_ne_zero_map_eq_zero` (2 declarations, 2 files)

- `theorem GSMultInterp.exists_ne_zero_map_eq_zero` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:214](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L214) — **Abstract underdetermined-system existence** (mirrors `BCKHS25.exists_ne_zero_map_eq_zero`): a line
- `theorem BCKHS25.exists_ne_zero_map_eq_zero` [ArkLib/Data/CodingTheory/ProximityGap/BCKHS25/Interpolation.lean:69](../../../ArkLib/Data/CodingTheory/ProximityGap/BCKHS25/Interpolation.lean#L69) — Abstract underdetermined-system existence: a linear map between finite-dimensional spaces with stric

### `exists_subset_card_eq_of_le_card` (2 declarations, 2 files)

- `lemma ProximityGap.exists_subset_card_eq_of_le_card` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6598](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6598) — Select exactly `r` elements from a finite set once its cardinality is large enough.  This is the fin
- `lemma ArkLib.Claim511.exists_subset_card_eq_of_le_card` [ArkLib/ToMathlib/Claim511.lean:119](../../../ArkLib/ToMathlib/Claim511.lean#L119) — Select exactly `r` elements from a finite set once its cardinality is large enough.  Final selection

### `extractability` (2 declarations, 2 files)

- `def Commitment.extractability` [ArkLib/CommitmentScheme/Basic.lean:202](../../../ArkLib/CommitmentScheme/Basic.lean#L202) — A commitment scheme satisfies **extractability** with error `extractabilityError` if there exists a 
- `def CommitmentScheme.extractability` [ArkLib/CommitmentScheme/CommitmentScheme.lean:159](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L159) — A commitment scheme satisfies **extractability** with error `extractabilityError` if there exists a 

### `extractor` (2 declarations, 2 files)

- `def CheckClaim.extractor` [ArkLib/ProofSystem/Component/CheckClaim.lean:120](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L120) — The round-by-round extractor for the `CheckClaim` reduction. Trivial since the witness is `Unit`.
- `def ReduceClaim.extractor` [ArkLib/ProofSystem/Component/ReduceClaim.lean:113](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L113) — The round-by-round extractor for the `ReduceClaim` (oracle) reduction. Requires a mapping `mapWitInv

### `failureProbability` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.failureProbability` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:130](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L130) — Paper-facing alias for CO25 Definition 3.7 failure probability.
- `def Verifier.failureProbability` [ArkLib/OracleReduction/Security/Rewinding.lean:163](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L163) — CO25 Definition 3.7, adapted to ArkLib's non-interactive verifier interface. The paper's size bound 

### `failureProbabilityFamily` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.failureProbabilityFamily` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:140](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L140) — Paper-facing alias for CO25 Definition 3.7 with explicit security parameter `λ`.
- `def Verifier.failureProbabilityFamily` [ArkLib/OracleReduction/Security/Rewinding.lean:248](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L248) — CO25 Definition 3.7 with the security parameter `λ` made explicit as an external index.

### `failureState` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.failureState` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:71](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L71) — A dummy state returned by the verifier upon failure of Check 1.
- `def RingSwitching.BatchingPhase.failureState` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:106](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L106) — A dummy state returned by the verifier upon failure of Check 1.

### `finSumFinEquiv_symm_dite` (2 declarations, 2 files)

- `theorem RingSwitching.finSumFinEquiv_symm_dite` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1531](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1531) — Value-form of `finSumFinEquiv.symm`: classify the index by whether its value is `< m`.
- `theorem ScratchRS.finSumFinEquiv_symm_dite` [ArkLib/ProofSystem/RingSwitching/Scratch.lean:28](../../../ArkLib/ProofSystem/RingSwitching/Scratch.lean#L28) — (no docstring)

### `finalSumcheckProverComputeMsg` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProverComputeMsg` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:543](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L543) — Pure prover message computation for FRI final sumcheck step.
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckProverComputeMsg` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:980](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L980) — Pure prover message computation: computes s' from the witness.

### `finalSumcheckProverWitOut` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProverWitOut` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:550](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L550) — Pure prover output witness for FRI final sumcheck step.
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckProverWitOut` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:987](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L987) — Pure prover output: computes the output witness given the transcript.

### `finalSumcheckVerifierCheck` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifierCheck` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:517](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L517) — Pure verifier check for FRI final sumcheck step.
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckVerifierCheck` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:962](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L962) — Pure verifier check: validates that s_{ℓ'} = eq_tilde_eval * s'. 8. `V` sets `e := eq̃(φ₀(r_κ), ...,

### `finalSumcheckVerifierStmtOut` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifierStmtOut` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:528](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L528) — Pure verifier output for FRI final sumcheck step.
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckVerifierStmtOut` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:971](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L971) — Pure verifier output: computes the output statement given the transcript.

### `firstOracleWitnessConsistency_unique` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.firstOracleWitnessConsistency_unique` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean:759](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean#L759) — (no docstring)
- `lemma Binius.RingSwitching.BBFSmallFieldIOPCS.firstOracleWitnessConsistency_unique` [ArkLib/ProofSystem/Binius/RingSwitching/BBFSmallFieldIOPCS.lean:171](../../../ArkLib/ProofSystem/Binius/RingSwitching/BBFSmallFieldIOPCS.lean#L171) — Uniqueness of the polynomial witness from first-oracle UDR-compatibility.

### `fixVars_eq_bind₁` (2 declarations, 2 files)

- `theorem RingSwitching.fixVars_eq_bind₁` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1545](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1545) — Characterization of `fixFirstVariablesOfMQP` as a `bind₁` partial substitution: it sends the survivi
- `theorem ScratchRS.fixVars_eq_bind₁` [ArkLib/ProofSystem/RingSwitching/Scratch.lean:35](../../../ArkLib/ProofSystem/RingSwitching/Scratch.lean#L35) — (no docstring)

### `fixVars_step` (2 declarations, 2 files)

- `theorem RingSwitching.fixVars_step` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1585](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1585) — **Round-transition for `fixFirstVariablesOfMQP` (cons form).** Fixing the last `v` variables of `pol
- `theorem ScratchRS.fixVars_step` [ArkLib/ProofSystem/RingSwitching/Scratch.lean:47](../../../ArkLib/ProofSystem/RingSwitching/Scratch.lean#L47) — (no docstring)

### `foldOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.foldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean:111](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean#L111) — (no docstring)
- `def Fri.Spec.FoldPhase.foldOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:516](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L516) — The oracle reduction that is the `i`-th round of the FRI protocol.

### `fullOracleVerifier_knowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_knowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:491](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L491) — Scalar KS for the full stack with error **`concreteFRIBiniusKnowledgeError`**, i.e. **DP24 §5.2 (43)
- `theorem Binius.RingSwitching.FullRingSwitching.fullOracleVerifier_knowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:501](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L501) — Scalar KS with error `fullRingSwitchingConcreteKnowledgeError κ L ℓ' ε_pcs` (Protocol 3.1 front + `ε

### `getEvaluationPointSuffix` (2 declarations, 2 files)

- `def Binius.RingSwitching.getEvaluationPointSuffix` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:377](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L377) — (no docstring)
- `def RingSwitching.getEvaluationPointSuffix` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:384](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L384) — (no docstring)

### `getSumcheckRoundPoly_eval_eq_sum_snoc` (2 declarations, 2 files)

- `theorem RingSwitching.SumcheckPhase.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:247](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L247) — **Target (b): `getSumcheckRoundPoly` value as a cube sum (LAST-variable/`snoc` form, defect-#20 repa
- `theorem Sumcheck.Structured.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:116](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L116) — **Round-univariate evaluation as a survivor-cube sum (last-variable / `snoc` form).** Evaluating the

### `guruswami_sudan_for_proximity_gap_existence` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:755](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L755) — Constructive witness extraction for the Guruswami–Sudan system. When the computable `hasWitnessC` ch
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:201](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L201) — The first part of Lemma 5.3 from [BCIKS20]. Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`pr

### `guruswami_sudan_for_proximity_gap_property` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:794](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L794) — Constructive witness property for the Guruswami–Sudan system. When `m > 0` and the codeword polynomi
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:213](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L213) — The second part of Lemma 5.3 from [BCIKS20]. For any solution `Q` of the Guruswami-Sudan system, and

### `ham_c0_c1` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c0_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:41](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L41) — Pairwise Hamming distances.
- `theorem JohnsonBound.JqlRefutation.ham_c0_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:80](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L80) — Pairwise Hamming distances.

### `ham_c0_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c0_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:42](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L42) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.ham_c0_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:81](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L81) — (no docstring)

### `ham_c1_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c1_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:43](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L43) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.ham_c1_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:82](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L82) — (no docstring)

### `hasseCoeff` (2 declarations, 2 files)

- `def GSMultInterp.hasseCoeff` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:135](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L135) — The order-`(a, b)` *Hasse coefficient* of the bivariate polynomial `Q = ∑_{(s,t)∈monoIdx} c(s,t)·X^s
- `def ArkLib.GS.hasseCoeff` [ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean:67](../../../ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean#L67) — The bivariate Hasse–Taylor coefficient of bidegree `(i, j)` of `Q` at `(a, b)`: take the `j`-th oute

### `heavyCoords_card_mul_le` (2 declarations, 2 files)

- `lemma ProximityGap.heavyCoords_card_mul_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6606](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6606) — Generic double-counting brick for Claim 5.11. If each `z ∈ S` has at most `m` bad coordinates, then 
- `lemma ArkLib.Claim511.heavyCoords_card_mul_le` [ArkLib/ToMathlib/Claim511.lean:78](../../../ArkLib/ToMathlib/Claim511.lean#L78) — **Double-counting brick.** If each `z ∈ S` has at most `m` bad coordinates, then the coordinates tha

### `hint` (2 declarations, 2 files)

- `def DomainSeparator.hint` [ArkLib/Data/Hash/DomainSep.lean:230](../../../ArkLib/Data/Hash/DomainSep.lean#L230) — Hint `count` native elements. Rust interface: ```rust pub fn hint(self, label: &str) -> Self ```
- `def HashStateWithInstructions.hint` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:191](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L191) — Process a hint operation. Rust interface: ```rust pub fn hint(&mut self) -> Result<(), DomainSeparat

### `hypercubeSplitEquiv` (2 declarations, 2 files)

- `def Binius.RingSwitching.hypercubeSplitEquiv` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:715](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L715) — The κ-then-ℓ' hypercube concatenation `concatBit v w i = v i` for `i < κ`, `= w (i - κ)` otherwise —
- `def RingSwitching.hypercubeSplitEquiv` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:805](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L805) — The κ-then-ℓ' hypercube concatenation `concatBit v w i = v i` for `i < κ`, `= w (i - κ)` otherwise —

### `instOracleVerifierAppendCoherent` (2 declarations, 2 files)

- `instance RingSwitching.BatchingPhase.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:219](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L219) — The batching-phase oracle verifier passes every output oracle through to the unchanged input oracle 
- `instance Sumcheck.Spec.SingleRound.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1357](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1357) — The `i`-th-round oracle verifier routes its (single) output oracle to the (unchanged) input oracle (

### `instOstmtMLIOPCS` (2 declarations, 2 files)

- `instance Binius.RingSwitching.instOstmtMLIOPCS` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:294](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L294) — (no docstring)
- `instance RingSwitching.instOstmtMLIOPCS` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:304](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L304) — (no docstring)

### `interpolate` (2 declarations, 2 files)

- `def ReedSolomon.interpolate` [ArkLib/Data/CodingTheory/ReedSolomon.lean:586](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L586) — The linear map that maps a codeword `f : ι → F` to a degree < \|ι\| polynomial p, such that `p(x) = f(
- `def UniPoly.Lagrange.interpolate` [ArkLib/Data/UniPoly/Basic.lean:1120](../../../ArkLib/Data/UniPoly/Basic.lean#L1120) — This function produces the polynomial which is of degree n and is equal to r i at ω^i for i = 0, 1, 

### `iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.QueryPhase.iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:315](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L315) — (no docstring)
- `lemma Binius.BinaryBasefold.iteratedQuotientMap_eq_qMap_total_fiber_extractMiddleFinMask` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean:516](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean#L516) — (no docstring)

### `iteratedSumcheckKStateProp` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckKStateProp` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:558](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L558) — KState for the iterated sumcheck step, matching the structure of Binary Basefold's `foldKStateProp`:
- `def RingSwitching.SumcheckPhase.iteratedSumcheckKStateProp` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:571](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L571) — This follows the KState of `foldKStateProp`

### `iteratedSumcheckKnowledgeStateFunction` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:601](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L601) — Knowledge state function (KState) for single round
- `def RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:625](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L625) — Knowledge state function (KState) for single round

### `iteratedSumcheckOracleProver` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleProver` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:153](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L153) — The prover for the `i`-th round of Ring Switching.
- `def RingSwitching.SumcheckPhase.iteratedSumcheckOracleProver` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:135](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L135) — (no docstring)

### `iteratedSumcheckOracleReduction` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:217](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L217) — The oracle reduction that is the `i`-th round of Ring Switching.
- `def RingSwitching.SumcheckPhase.iteratedSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:160](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L160) — (no docstring)

### `iteratedSumcheckOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:330](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L330) — (no docstring)
- `theorem RingSwitching.SumcheckPhase.iteratedSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:207](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L207) — Iterated-sumcheck round completeness from the explicit local algebraic residual.

### `iteratedSumcheckOracleVerifier` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:188](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L188) — The oracle verifier for the `i`-th round of Ring Switching.
- `def RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:148](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L148) — (no docstring)

### `iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:883](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L883) — RBR knowledge soundness for a single round oracle verifier
- `theorem RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:653](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L653) — RBR knowledge soundness for one sumcheck round under the current weak post-challenge state. The boun

### `iteratedSumcheckPrvState` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckPrvState` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:143](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L143) — The state maintained by the prover throughout the sumcheck phase.
- `def RingSwitching.SumcheckPhase.iteratedSumcheckPrvState` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:122](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L122) — (no docstring)

### `iteratedSumcheckRbrExtractor` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:531](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L531) — (no docstring)
- `def RingSwitching.SumcheckPhase.iteratedSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:506](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L506) — (no docstring)

### `iteratedSumcheckRoundKnowledgeError` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckRoundKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:521](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L521) — (no docstring)
- `def RingSwitching.SumcheckPhase.iteratedSumcheckRoundKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1295](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1295) — Per-round knowledge error for the iterated sumcheck rounds.

### `iterated_fold_to_const_strict` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.iterated_fold_to_const_strict` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:977](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L977) — **Strict version**: When folding the last oracle to level `ℓ` (final sumcheck), the iterated fold of
- `lemma Binius.FRIBinius.CoreInteractionPhase.iterated_fold_to_const_strict` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:711](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L711) — Strict helper: folding the last oracle block in the final sumcheck step yields the constant function

### `leftpad` (2 declarations, 2 files)

- `def Fin.leftpad` [ArkLib/Data/Fin/Tuple/Defs.lean:96](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L96) — Pad a `Fin`-indexed vector on the left with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.leftpad` [ArkLib/Data/Matrix/Basic.lean:25](../../../ArkLib/Data/Matrix/Basic.lean#L25) — (no docstring)

### `liftContext_completeness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:241](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L241) — STATEMENT REPAIR (2026-06-04): completeness lifting now additionally takes the verifier's oracle-rou
- `theorem Reduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:776](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L776) — Lifting the reduction preserves completeness, assuming the lens satisfies its completeness condition

### `liftContext_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:288](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L288) — (no docstring)
- `theorem Verifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1060](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1060) — (no docstring)

### `liftContext_perfectCompleteness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:251](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L251) — (no docstring)
- `theorem Reduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:881](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L881) — (no docstring)

### `liftContext_rbr_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:346](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L346) — (no docstring)
- `theorem Verifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1804](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1804) — (no docstring)

### `liftContext_rbr_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:307](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L307) — (no docstring)
- `theorem Verifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1556](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1556) — (no docstring)

### `liftContext_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:274](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L274) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions. STA
- `theorem Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:955](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L955) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions

### `list_reduceOption_helper` (2 declarations, 2 files)

- `lemma ReedSolomon.Finset.list_reduceOption_helper` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:256](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L256) — (no docstring)
- `lemma Finset.list_reduceOption_helper` [ArkLib/ToMathlib/Finset/ToListWithProof.lean:43](../../../ArkLib/ToMathlib/Finset/ToListWithProof.lean#L43) — (no docstring)

### `mem_C_iff` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.mem_C_iff` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:46](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L46) — Membership in `C` is membership in the explicit three-element set.
- `theorem JohnsonBound.JqlRefutation.mem_C_iff` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:85](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L85) — Membership in `C` is membership in the explicit three-element set.

### `mem_subgroup_iff_mem_domain` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.mem_subgroup_iff_mem_domain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:324](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L324) — (no docstring)
- `lemma Domain.FftDomainClass.mem_subgroup_iff_mem_domain` [ArkLib/Data/Domain/FftDomain/ToSubgroup.lean:67](../../../ArkLib/Data/Domain/FftDomain/ToSubgroup.lean#L67) — (no docstring)

### `mem_subgroup_iff_mem_finset` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.mem_subgroup_iff_mem_finset` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:318](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L318) — (no docstring)
- `lemma Domain.FftDomainClass.mem_subgroup_iff_mem_finset` [ArkLib/Data/Domain/FftDomain/ToSubgroup.lean:60](../../../ArkLib/Data/Domain/FftDomain/ToSubgroup.lean#L60) — (no docstring)

### `mem_support_simulateQ_id'_liftM_query` (2 declarations, 2 files)

- `lemma OptionT.mem_support_simulateQ_id'_liftM_query` [ArkLib/ToVCVio/Lemmas.lean:430](../../../ArkLib/ToVCVio/Lemmas.lean#L430) — **Generic**: any element of the range of a query is in the support of `simulateQ (fun t => liftM (qu
- `lemma mem_support_simulateQ_id'_liftM_query` [ArkLib/ToVCVio/Simulation.lean:217](../../../ArkLib/ToVCVio/Simulation.lean#L217) — (no docstring)

### `minDist_C` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.minDist_C` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:51](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L51) — Every distinct pair of codewords has Hamming distance `≥ 1`, and the pair `(c0, c1)` attains `1`. He
- `theorem JohnsonBound.JqlRefutation.minDist_C` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:93](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L93) — **`Code.minDist C = 1`.**  The defining set of distinct-pair distances is `{1, 2}` (`d(c0,c1) = d(c0

### `neg_one_mem_domain` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.neg_one_mem_domain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:419](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L419) — (no docstring)
- `lemma Domain.FftDomainClass.neg_one_mem_domain` [ArkLib/Data/Domain/FftDomain/Ops.lean:82](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L82) — (no docstring)

### `ofFinCoeff` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.Rq.ofFinCoeff` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:184](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L184) — The reduced representative with prescribed finite coefficients `Σ_{k<N} cₖ Xᵏ`, valid when `N` does 
- `def CompPoly.CPolynomial.ofFinCoeff` [ArkLib/ToCompPoly/Univariate/Basic.lean:293](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L293) — The polynomial with prescribed finite coefficient function: `Σ_{k<N} cₖ Xᵏ`.

### `oracleVerifier_toVerifier_run` (2 declarations, 2 files)

- `theorem ReduceClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/ReduceClaim.lean:207](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L207) — Running the (oracle) verifier of the `ReduceClaim` oracle reduction deterministically returns the ma
- `theorem SendSingleWitness.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendWitness.lean:248](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L248) — (no docstring)

### `pSpecBatching` (2 declarations, 2 files)

- `def Binius.RingSwitching.pSpecBatching` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:53](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L53) — (no docstring)
- `def RingSwitching.pSpecBatching` [ArkLib/ProofSystem/RingSwitching/Spec.lean:34](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L34) — (no docstring)

### `pSpecFinalSumcheck` (2 declarations, 2 files)

- `def Binius.RingSwitching.pSpecFinalSumcheck` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:67](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L67) — (no docstring)
- `def RingSwitching.pSpecFinalSumcheck` [ArkLib/ProofSystem/RingSwitching/Spec.lean:47](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L47) — (no docstring)

### `pSpecFold` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecFold` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:201](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L201) — (no docstring)
- `def Fri.Spec.pSpecFold` [ArkLib/ProofSystem/Fri/Spec/General.lean:66](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L66) — (no docstring)

### `pSpecLargeFieldReduction` (2 declarations, 2 files)

- `def Binius.RingSwitching.pSpecLargeFieldReduction` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:73](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L73) — (no docstring)
- `def RingSwitching.pSpecLargeFieldReduction` [ArkLib/ProofSystem/RingSwitching/Spec.lean:53](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L53) — (no docstring)

### `pSpecSumcheckLoop` (2 declarations, 2 files)

- `def Binius.RingSwitching.pSpecSumcheckLoop` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:64](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L64) — (no docstring)
- `def RingSwitching.pSpecSumcheckLoop` [ArkLib/ProofSystem/RingSwitching/Spec.lean:45](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L45) — (no docstring)

### `packMLE` (2 declarations, 2 files)

- `def Binius.RingSwitching.packMLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:114](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L114) — **Definition 2.1 (MLE packing)**. Packs a small-field multilinear `t` into a large-field multilinear
- `def RingSwitching.packMLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:113](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L113) — **Definition 2.1 (MLE packing)**. Packs a small-field multilinear `t` into a large-field multilinear

### `packMLE_repr_eval` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.packMLE_repr_eval` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:575](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L575) — The basis coordinate of a packed evaluation recovers the small-field coefficient: `β.repr (t'(w)) u 
- `lemma RingSwitching.packMLE_repr_eval` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:691](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L691) — The basis coordinate of a packed evaluation recovers the small-field coefficient: `β.repr (t'(w)) u 

### `perfectCorrectness` (2 declarations, 2 files)

- `def Commitment.perfectCorrectness` [ArkLib/CommitmentScheme/Basic.lean:109](../../../ArkLib/CommitmentScheme/Basic.lean#L109) — A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
- `def CommitmentScheme.perfectCorrectness` [ArkLib/CommitmentScheme/CommitmentScheme.lean:74](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L74) — A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.

### `perfectlyCorrect` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Ajtai.InnerOuter.perfectlyCorrect` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Correctness.lean:198](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Correctness.lean#L198) — **Unconditional perfect correctness with the concrete binary decomposition.** Both message and inner
- `theorem ArkLib.Lattices.Ajtai.Simple.perfectlyCorrect` [ArkLib/CommitmentScheme/Ajtai/Simple/Correctness.lean:33](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Correctness.lean#L33) — Simple Ajtai commitments are correct on short messages: an honest commitment to a message accepted b

### `performCheckOriginalEvaluation` (2 declarations, 2 files)

- `def Binius.RingSwitching.performCheckOriginalEvaluation` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:339](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L339) — Step 2 (V): Check 1: s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v. Note (soundness fix): the de
- `def RingSwitching.performCheckOriginalEvaluation` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:347](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L347) — Step 2 (V): Check 1: s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v. Note (soundness fix): the de

### `performCheckOriginalEvaluation_packMLE_iff` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.performCheckOriginalEvaluation_packMLE_iff` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:805](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L805) — **DP24 ring-switching capstone (decision form).** The verifier's Step-2 check on the prover's honest
- `lemma RingSwitching.performCheckOriginalEvaluation_packMLE_iff` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:980](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L980) — **Generic DP24 ring-switching capstone (decision form)** over an abstract `P`. The verifier's Step-2

### `pow_eq_card_eq_zero_or_gcd` (2 declarations, 2 files)

- `theorem ProximityGap.MultiplicativeRigidity.pow_eq_card_eq_zero_or_gcd` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean#L63) — **Lemma 1 (monomial agreement / coset rigidity).** In a finite cyclic commutative group `G` of order
- `theorem MultiplicativeRigidity.pow_eq_card_eq_zero_or_gcd` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean:100](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean#L100) — **Coset rigidity / monomial agreement (core).** In a finite cyclic group `G` of order `n = Fintype.c

### `prod_concat_split` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.prod_concat_split` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:627](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L627) — A product over `Fin (ℓ' + κ₀)` of a function defined by the κ/ℓ'-dichotomy splits as the product of 
- `lemma RingSwitching.prod_concat_split` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:719](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L719) — A product over `Fin (ℓ' + κ₀)` of a function defined by the κ/ℓ'-dichotomy splits as the product of 

### `prop_4_23_singleRepetition_proximityCheck_bound` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.QueryPhase.prop_4_23_singleRepetition_proximityCheck_bound` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:2688](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L2688) — **Single Repetition Proximity Check Bound (Proposition 4.24)** For a single repetition of the proxim
- `theorem Binius.BinaryBasefold.prop_4_23_singleRepetition_proximityCheck_bound` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhaseSoundness.lean:1267](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhaseSoundness.lean#L1267) — **Proposition 4.24** (Query-phase soundness, assuming no bad events). If any oracle is non-compliant

### `proximityCondition` (2 declarations, 2 files)

- `def MutualCorrAgreement.proximityCondition` [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:56](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean#L56) — For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽` and linea
- `def Generator.proximityCondition` [ArkLib/ProofSystem/Whir/ProximityGen.lean:38](../../../ArkLib/ProofSystem/Whir/ProximityGen.lean#L38) — For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽ˡ` and linear 

### `queryCodeword` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryCodeword` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean:149](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean#L149) — Oracle query helper: query a committed codeword at a given domain point. Restricted to codeword indi
- `def Fri.Spec.QueryRound.queryCodeword` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:1016](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L1016) — (no docstring)

### `queryOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:172](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L172) — The oracle reduction for the final query phase.
- `def Fri.Spec.QueryRound.queryOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:1134](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L1134) — (no docstring)

### `reduction_verifier_eq_verifier` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:193](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L193) — (no docstring)
- `lemma Sumcheck.Spec.SingleRound.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1393](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1393) — (no docstring)

### `relIn` (2 declarations, 2 files)

- `def CheckClaim.relIn` [ArkLib/ProofSystem/Component/CheckClaim.lean:60](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L60) — (no docstring)
- `def RandomQuery.relIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:41](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L41) — The input relation is that the two oracles are equal.

### `rewindingKnowledgeSoundness` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.rewindingKnowledgeSoundness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:157](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L157) — Paper-facing alias for CO25 Definition 3.8 rewinding knowledge soundness.
- `def Verifier.rewindingKnowledgeSoundness` [ArkLib/OracleReduction/Security/Rewinding.lean:211](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L211) — CO25 Definition 3.8, adapted to ArkLib's non-interactive argument interface. ArkLib's `Prover.NARG` 

### `rewindingKnowledgeSoundnessFamily` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.rewindingKnowledgeSoundnessFamily` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:174](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L174) — Paper-facing alias for CO25 Definition 3.8 with explicit security parameter `λ`.
- `def Verifier.rewindingKnowledgeSoundnessFamily` [ArkLib/OracleReduction/Security/Rewinding.lean:263](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L263) — CO25 Definition 3.8 with the security parameter `λ` made explicit as an external index. This is a wr

### `rightpad` (2 declarations, 2 files)

- `def Fin.rightpad` [ArkLib/Data/Fin/Tuple/Defs.lean:90](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L90) — Pad a `Fin`-indexed vector on the right with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.rightpad` [ArkLib/Data/Matrix/Basic.lean:21](../../../ArkLib/Data/Matrix/Basic.lean#L21) — (no docstring)

### `roundKnowledgeError` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckPhase.roundKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:228](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L228) — Repaired local bound for the current round-by-round proof. The sharp `2 / \|L\|` statement needs the u
- `def Sumcheck.Structured.roundKnowledgeError` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:364](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L364) — Round-by-round knowledge error for a single round of the structured sumcheck: the Schwartz–Zippel bo

### `rs_lambda_high_rate_jh01` (2 declarations, 2 files)

- `theorem CodingTheory.rs_lambda_high_rate_jh01` [ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean:1736](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean#L1736) — **ABF26 Theorem 3.14 [JH01 Thm 2], repaired list-size form.** Large-rate Reed-Solomon lower bound. F
- `theorem CodingTheory.ReedSolomon.rs_lambda_high_rate_jh01` [ArkLib/Data/CodingTheory/ListDecoding/JH01.lean:210](../../../ArkLib/Data/CodingTheory/ListDecoding/JH01.lean#L210) — ABF26 Theorem 3.14 / JH01 Theorem 2, in a repaired list-size form.  For every `j ≥ 2`, infinitely ma

### `run` (2 declarations, 2 files)

- `def AGM.Adversary.run` [ArkLib/AGM/Basic.lean:168](../../../ArkLib/AGM/Basic.lean#L168) — Running the adversary on a given table, returning the list of group elements it is supposed to outpu
- `def Prover.run` [ArkLib/OracleReduction/Execution.lean:146](../../../ArkLib/OracleReduction/Execution.lean#L146) — Run the prover in an interactive reduction. Returns the output statement and witness, and the transc

### `shiftSeries` (2 declarations, 2 files)

- `def ArkLib.Claim59Conditional.shiftSeries` [ArkLib/ToMathlib/Claim59Conditional.lean:51](../../../ArkLib/ToMathlib/Claim59Conditional.lean#L51) — The BCIKS shift series corresponding to the substitution $X \mapsto X - x_0$.
- `def ArkLib.SubstFieldCaveat.shiftSeries` [ArkLib/ToMathlib/SubstFieldCaveat.lean:70](../../../ArkLib/ToMathlib/SubstFieldCaveat.lean#L70) — The shift series corresponding to the substitution $X \mapsto X - x_0$.

### `simulateQ_oracleVerify_eq` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.SingleRound.Simple.simulateQ_oracleVerify_eq` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:965](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L965) — Closed form of the simulated oracle-verifier `verify`: the inner `simOracle2` simulation collapses t
- `theorem ToyProblem.Spec.simulateQ_oracleVerify_eq` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:774](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L774) — **Closed form of the compiled toy-problem oracle verifier.** Simulating `oracleVerifier.verify` agai

### `singleEq_collapse` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.singleEq_collapse` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:491](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L491) — A single `eqPolynomial` factor, evaluated through the mixed embedding `eval₂ φ₁ (φ₀ ∘ g)` at a Boole
- `lemma RingSwitching.singleEq_collapse` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:638](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L638) — A single `eqPolynomial` factor, evaluated through the mixed embedding `eval₂ φ₁ (φ₀ ∘ g)` at a Boole

### `size_of_smooth_coset_domain_eq_pow_of_2` (2 declarations, 2 files)

- `lemma ReedSolomon.CosetFftDomain.size_of_smooth_coset_domain_eq_pow_of_2` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1317](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1317) — (no docstring)
- `lemma Domain.size_of_smooth_coset_domain_eq_pow_of_2` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:493](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L493) — Compatibility form of the smooth-coset domain size: the `toFinset` of a `SmoothCosetFftDomain n F` h

### `sq_root_mem_subdomain` (2 declarations, 2 files)

- `lemma ReedSolomon.CosetFftDomain.sq_root_mem_subdomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1586](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1586) — (no docstring)
- `lemma Domain.CosetFftDomainClass.sq_root_mem_subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:394](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L394) — (no docstring)

### `subdomain_embed` (2 declarations, 2 files)

- `def ReedSolomon.FftDomain.subdomain_embed` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:774](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L774) — (no docstring)
- `def Domain.CosetFftDomainClass.subdomain_embed` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:44](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L44) — (no docstring)

### `subdomain_embed_add` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.subdomain_embed_add` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:784](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L784) — (no docstring)
- `lemma Domain.CosetFftDomainClass.subdomain_embed_add` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:56](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L56) — (no docstring)

### `subdomain_embed_injective` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.subdomain_embed_injective` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:798](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L798) — (no docstring)
- `lemma Domain.CosetFftDomainClass.subdomain_embed_injective` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:74](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L74) — (no docstring)

### `subdomain_embed_of_le` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.subdomain_embed_of_le` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:873](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L873) — (no docstring)
- `lemma Domain.CosetFftDomainClass.subdomain_embed_of_le` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:254](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L254) — (no docstring)

### `subdomain_embed_zero` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.subdomain_embed_zero` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:793](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L793) — (no docstring)
- `lemma Domain.CosetFftDomainClass.subdomain_embed_zero` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:69](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L69) — (no docstring)

### `sumcheckConsistencyProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.sumcheckConsistencyProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1089](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1089) — Sumcheck consistency: the claimed sumcheck target equals the sum of `H` over the boolean hypercube o
- `def Sumcheck.Structured.sumcheckConsistencyProp` [ArkLib/ProofSystem/Sumcheck/Structured.lean:212](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L212) — Sumcheck consistency: the claimed sum equals the actual polynomial evaluation sum over the evaluatio

### `sumcheckConsistency_at_last_simplifies` (2 declarations, 2 files)

- `lemma Binius.FRIBinius.CoreInteractionPhase.sumcheckConsistency_at_last_simplifies` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:663](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L663) — At `Fin.last ℓ'`, sumcheck consistency simplifies to a single evaluation.
- `lemma Binius.RingSwitching.SumcheckPhase.sumcheckConsistency_at_last_simplifies` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1036](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1036) — At `Fin.last ℓ'`, the sumcheck consistency sum is over 0 variables, simplifying to a single evaluati

### `sumcheckFoldOracleReduction` (2 declarations, 2 files)

- `def sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:793](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L793) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:154](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L154) — (no docstring)

### `sumcheckFoldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:895](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L895) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:252](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L252) — (no docstring)

### `sumcheckFoldOracleVerifier` (2 declarations, 2 files)

- `def sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:512](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L512) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:147](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L147) — (no docstring)

### `sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1046](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1046) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:421](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L421) — (no docstring)

### `sumcheckLoopOracleReduction` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.sumcheckLoopOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1681](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1681) — Composed oracle reduction for the SumcheckStep (seqCompose over ℓ')
- `def RingSwitching.SumcheckPhase.sumcheckLoopOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1162](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1162) — Composed oracle reduction for the SumcheckStep (seqCompose over ℓ')

### `sumcheckLoopOracleVerifier` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.sumcheckLoopOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1672](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1672) — Composed oracle verifier for the SumcheckStep (seqCompose over ℓ')
- `def RingSwitching.SumcheckPhase.sumcheckLoopOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1143](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1143) — Composed oracle verifier for the SumcheckStep (seqCompose over ℓ')

### `sumcheckRoundRelation` (2 declarations, 2 files)

- `def Binius.RingSwitching.sumcheckRoundRelation` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:447](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L447) — Input relation for single round: proper sumcheck statement
- `def RingSwitching.sumcheckRoundRelation` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:461](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L461) — Input relation for single round: proper sumcheck statement

### `sumcheckRoundRelationProp` (2 declarations, 2 files)

- `def Binius.RingSwitching.sumcheckRoundRelationProp` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:440](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L440) — (no docstring)
- `def RingSwitching.sumcheckRoundRelationProp` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:454](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L454) — (no docstring)

### `sumcheckSum_X0_eq` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.sumcheckSum_X0_eq` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:849](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L849) — **Sumcheck hypercube sum depends on the evaluation domain `𝓑`.** The single-variable sumcheck consis
- `lemma RingSwitching.sumcheckSum_X0_eq` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1309](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1309) — **Sumcheck hypercube sum depends on the evaluation domain `𝓑`.** The single-variable sumcheck consis

### `sumcheckTarget_domain_indep` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.sumcheckTarget_domain_indep` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:868](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L868) — **No `𝓑`-free target satisfies sumcheck consistency for all domains `𝓑`.** If a single value `c` (in
- `lemma RingSwitching.sumcheckTarget_domain_indep` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1328](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1328) — **No `𝓑`-free target satisfies sumcheck consistency for all domains `𝓑`.** If a single value `c` (in

### `support_liftComp` (2 declarations, 2 files)

- `theorem OracleComp.support_liftComp` [ArkLib/ToMathlib/AppendHelpers.lean:30](../../../ArkLib/ToMathlib/AppendHelpers.lean#L30) — The monadic lifting operation `liftComp` preserves the support of a computation. Specifically, for a
- `lemma support_liftComp` [ArkLib/ToVCVio/Lemmas.lean:525](../../../ArkLib/ToVCVio/Lemmas.lean#L525) — (no docstring)

### `support_mk` (2 declarations, 2 files)

- `lemma ReduceClaim.support_mk` [ArkLib/ProofSystem/Component/ReduceClaim.lean:128](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L128) — (no docstring)
- `lemma OptionT.support_mk` [ArkLib/ToVCVio/Lemmas.lean:106](../../../ArkLib/ToVCVio/Lemmas.lean#L106) — (no docstring)

### `toListWithProof.` (2 declarations, 2 files)

- `def ReedSolomon.Finset.toListWithProof.` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:238](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L238) — A helper to convert a finset into a list whose elements are the members of the finset, i.e. come wit
- `def Finset.toListWithProof.` [ArkLib/ToMathlib/Finset/ToListWithProof.lean:25](../../../ArkLib/ToMathlib/Finset/ToListWithProof.lean#L25) — A helper to convert a finset into a list whose elements are the members of the finset, i.e. come wit

### `toListWithProof_empty.` (2 declarations, 2 files)

- `lemma ReedSolomon.Finset.toListWithProof_empty.` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:245](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L245) — (no docstring)
- `lemma Finset.toListWithProof_empty.` [ArkLib/ToMathlib/Finset/ToListWithProof.lean:32](../../../ArkLib/ToMathlib/Finset/ToListWithProof.lean#L32) — (no docstring)

### `toListWithProof_eq_toList.` (2 declarations, 2 files)

- `lemma ReedSolomon.Finset.toListWithProof_eq_toList.` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:272](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L272) — (no docstring)
- `lemma Finset.toListWithProof_eq_toList.` [ArkLib/ToMathlib/Finset/ToListWithProof.lean:59](../../../ArkLib/ToMathlib/Finset/ToListWithProof.lean#L59) — (no docstring)

### `toListWithProof_mem.` (2 declarations, 2 files)

- `lemma ReedSolomon.Finset.toListWithProof_mem.` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:249](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L249) — (no docstring)
- `lemma Finset.toListWithProof_mem.` [ArkLib/ToMathlib/Finset/ToListWithProof.lean:36](../../../ArkLib/ToMathlib/Finset/ToListWithProof.lean#L36) — (no docstring)

### `toMonadDecoration` (2 declarations, 2 files)

- `def Interaction.OracleDecoration.toMonadDecoration` [ArkLib/Interaction/Oracle/Core.lean:793](../../../ArkLib/Interaction/Oracle/Core.lean#L793) — Compute the per-node `MonadDecoration` from an oracle decoration and accumulated oracle spec. Sender
- `def Interaction.Oracle.Spec.toMonadDecoration` [ArkLib/Interaction/Oracle/Spec.lean:184](../../../ArkLib/Interaction/Oracle/Spec.lean#L184) — Compute the per-node `MonadDecoration` for the verifier on `toInteractionSpec`. - At `.oracle` nodes

### `toOracleSpec` (2 declarations, 2 files)

- `def Interaction.Oracle.Spec.toOracleSpec` [ArkLib/Interaction/Oracle/Spec.lean:149](../../../ArkLib/Interaction/Oracle/Spec.lean#L149) — The oracle specification for querying oracle messages along a given `PublicTranscript` path. Maps ea
- `def OracleInterface.toOracleSpec` [ArkLib/OracleReduction/OracleInterface.lean:92](../../../ArkLib/OracleReduction/OracleInterface.lean#L92) — Converts an indexed type family of oracle interfaces into an oracle specification. Notation: `[v]ₒ` 

### `twoNthRoot_correct_one` (2 declarations, 2 files)

- `lemma ReedSolomon.CosetFftDomain.twoNthRoot_correct_one` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1940](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1940) — (no docstring)
- `lemma Domain.CosetFftDomain.twoNthRoot_correct_one` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:475](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L475) — (no docstring)

### `unpackMLE` (2 declarations, 2 files)

- `def Binius.RingSwitching.unpackMLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:144](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L144) — **Unpacking a Packed Multilinear Polynomial**. Reverses the packing defined in `packMLE`. It reconst
- `def RingSwitching.unpackMLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:143](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L143) — **Unpacking a Packed Multilinear Polynomial**. Reverses the packing defined in `packMLE`. It reconst

### `val_eq_nsmul_one` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.val_eq_nsmul_one` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:481](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L481) — (no docstring)
- `lemma Domain.FftDomainClass.val_eq_nsmul_one` [ArkLib/Data/Domain/FftDomain/Ops.lean:113](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L113) — (no docstring)

### `vanishesToOrder` (2 declarations, 2 files)

- `def GSMultInterp.vanishesToOrder` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:152](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L152) — `Q` (given by coefficient vector `c`) **vanishes to order `m`** at `(x₀, y₀)`: every Hasse coefficie
- `def ArkLib.GS.vanishesToOrder` [ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean#L60) — `Q : F[X][Y]` **vanishes to order `m` at `(a, b)`** when, for every `Y`-index `j`, the inner Taylor 

### `vecL2NormSq` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:91](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L91) — Centered squared-`ℓ₂` norm of a vector: the sum of entrywise norms.
- `def ArkLib.Lattices.CenteredCoeffView.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/Norms.lean:80](../../../ArkLib/Data/Lattices/CyclotomicRing/Norms.lean#L80) — Vector squared `ℓ₂` norm: the sum of entrywise squared `ℓ₂` norms.

### `verifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem DoNothing.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:57](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L57) — The `DoNothing` verifier is perfectly round-by-round knowledge sound.
- `theorem ReduceClaim.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:171](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L171) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s

### `verifyOpening` (2 declarations, 2 files)

- `def KZG.verifyOpening` [ArkLib/CommitmentScheme/KZG/Basic.lean:69](../../../ArkLib/CommitmentScheme/KZG/Basic.lean#L69) — To verify a KZG opening `opening` for a commitment `commitment` at point `z` with claimed evaluation
- `def InductiveMerkleTree.verifyOpening` [ArkLib/CommitmentScheme/MerkleTree/Batch.lean:104](../../../ArkLib/CommitmentScheme/MerkleTree/Batch.lean#L104) — Verify one packaged opening against a claimed root, in `OptionT (OracleComp ...)`.

### `weight_Λ_over_𝒪_add_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_add_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:635](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L635) — `Λ_𝒪(a + b) ≤ max(Λ_𝒪 a, Λ_𝒪 b)`: sub-additivity over `𝒪 H`.
- `lemma ArkLib.weight_Λ_over_𝒪_add_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:81](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L81) — Sub-additivity of the `𝒪`-weight under addition: `Λ(a + b) ≤ max (Λ a) (Λ b)`.

### `weight_Λ_over_𝒪_mul_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_mul_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:620](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L620) — `Λ_𝒪(a · b) ≤ Λ_𝒪(a) + Λ_𝒪(b)`: sub-multiplicativity over `𝒪 H`.  Take the canonical representatives
- `lemma ArkLib.weight_Λ_over_𝒪_mul_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:142](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L142) — Sub-multiplicativity of the `𝒪`-weight: `Λ(a · b) ≤ Λ a + Λ b`. This is the central inequality the A

### `weight_Λ_over_𝒪_neg` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_neg` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:650](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L650) — `Λ_𝒪(-a) = Λ_𝒪(a)`: the `𝒪`-weight is negation-invariant (`mk (-ra) = -a`, `weight_Λ_neg`).
- `lemma ArkLib.weight_Λ_over_𝒪_neg` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:98](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L98) — Sub-additivity of the `𝒪`-weight under negation: it is invariant.

### `weight_Λ_over_𝒪_pow_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_pow_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:676](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L676) — `Λ_𝒪(a ^ k) ≤ k • Λ_𝒪(a)` (i.e. `≤ k · Λ_𝒪(a)` in `WithBot ℕ`): the power bound over `𝒪 H`, by induc
- `lemma ArkLib.weight_Λ_over_𝒪_pow_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:157](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L157) — Sub-multiplicativity for powers: `Λ(a ^ n) ≤ n • Λ a` (with `0 • Λ a = 0`, matching `weight_Λ_over_𝒪

### `weight_Λ_over_𝒪_sum_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_sum_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:662](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L662) — `Λ_𝒪(∑ᵢ f i) ≤ sup of Λ_𝒪(f i)`: the `𝒪`-weight of a finite sum is bounded by the sup of the summand
- `lemma ArkLib.weight_Λ_over_𝒪_sum_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:123](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L123) — The `𝒪`-weight of a finite sum is bounded by the `sup` of the summands' weights.

### `OracleInterface` (3 declarations, 2 files)

- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:88](../../../ArkLib/OracleReduction/Basic.lean#L88) — (no docstring)
- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:162](../../../ArkLib/OracleReduction/Basic.lean#L162) — (no docstring)
- `class OracleInterface` [ArkLib/OracleReduction/OracleInterface.lean:52](../../../ArkLib/OracleReduction/OracleInterface.lean#L52) — `OracleInterface` is a type class that provides an oracle interface for a type `Message`. It consist

### `card_agreement_le` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.card_agreement_le` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:102](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L102) — The agreement set of two distinct codewords' polynomials (inside any subtype of `F`) has at most `de
- `lemma OutOfDomSmpl.card_agreement_le` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:208](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L208) — Two distinct smooth codewords' decoded polynomials agree on at most `2^m - 1` field points: agreemen

### `card_filter_forall_pi` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.card_filter_forall_pi` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:71](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L71) — Counting a coordinatewise event: the tuples satisfying `Q` in every coordinate form the `piFinset` o
- `lemma OutOfDomSmpl.card_filter_forall_pi` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:180](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L180) — Tuples satisfying `Q` in every coordinate form the `piFinset` of the per-coordinate solution set, so

### `coeff_ehQ_eq_leading` (2 declarations, 2 files)

- `lemma MvPolynomial.coeff_ehQ_eq_leading` [ArkLib/ToMathlib/RestrictedSumset.lean:220](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L220) — The coefficient of the top monomial `X₀^{n-1} X₁^{n-2}` in `ehQ C'` (with `\|C'\| = 2(n-2)`) equals it
- `lemma MvPolynomial.coeff_ehQ_eq_leading` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:269](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L269) — `ehQ h Cset` differs from the leading part `vdmX h · y^{\|Cset\|}` by a polynomial of strictly smaller

### `coeff_zero_of_natDegree_lt` (2 declarations, 2 files)

- `lemma ProximityGap.coeff_zero_of_natDegree_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:693](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L693) — (no docstring)
- `lemma ProximityGap.coeff_zero_of_natDegree_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:31](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L31) — (no docstring)

### `decodeLT_ne_of_val_ne` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:87](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L87) — Distinct codewords decode to distinct polynomials: the decoded polynomial interpolates the codeword 
- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:194](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L194) — Distinct smooth codewords decode to distinct univariate polynomials (the decoded polynomial interpol

### `ehQ` (2 declarations, 2 files)

- `def MvPolynomial.ehQ` [ArkLib/ToMathlib/RestrictedSumset.lean:215](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L215) — **The Erdős–Heilbronn polynomial** for a padded sumset `C'`.
- `def MvPolynomial.ehQ` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:264](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L264) — **The general Erdős–Heilbronn polynomial** for a padded sumset `C'`.

### `ehY` (2 declarations, 2 files)

- `def MvPolynomial.ehY` [ArkLib/ToMathlib/RestrictedSumset.lean:164](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L164) — Abbreviation for the "diagonal" variable `y = X₀ + X₁`.
- `def MvPolynomial.ehY` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:182](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L182) — The "diagonal" variable `y = ∑_k X k`.

### `eval_ehQ_eq_zero` (2 declarations, 2 files)

- `lemma MvPolynomial.eval_ehQ_eq_zero` [ArkLib/ToMathlib/RestrictedSumset.lean:291](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L291) — `ehQ Cset` vanishes at every point `s : Fin 2 → F` whose two coordinates either coincide, or sum to 
- `lemma MvPolynomial.eval_ehQ_eq_zero` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:326](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L326) — `ehQ h Cset` vanishes at every point `s : Fin h → F` whose coordinates are not all distinct, or whos

### `finset_card_ge_of_pred_natCast_le_ennreal_lt` (2 declarations, 2 files)

- `lemma ProximityGap.finset_card_ge_of_pred_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:126](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L126) — (no docstring)
- `theorem ProximityGap.finset_card_ge_of_pred_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:131](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L131) — Convert an ENNReal lower bound on a finite set cardinality into a natural number weak cardinality bo

### `finset_card_gt_of_natCast_le_ennreal_lt` (2 declarations, 2 files)

- `lemma ProximityGap.finset_card_gt_of_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:119](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L119) — (no docstring)
- `theorem ProximityGap.finset_card_gt_of_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:120](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L120) — Convert an ENNReal lower bound on a finite set cardinality into a natural number strict cardinality 

### `prizeRate_floor_add_one_le` (2 declarations, 2 files)

- `lemma ProximityGap.prizeRate_floor_add_one_le` [ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeDecision.lean:149](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeDecision.lean#L149) — For `n ≥ 2`, every prize-rate degree satisfies `k_j + 1 ≤ n`.
- `lemma ProximityGap.prizeRate_floor_add_one_le` [ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean:371](../../../ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean#L371) — For `n ≥ 2`, every prize-rate degree satisfies `k_j + 1 ≤ n`.

### `prizeRates_le_half` (2 declarations, 2 files)

- `lemma ProximityGap.prizeRates_le_half` [ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeDecision.lean:141](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeDecision.lean#L141) — Every prize rate is `≤ 1/2`.
- `lemma ProximityGap.prizeRates_le_half` [ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean:363](../../../ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean#L363) — Every prize rate is at most `1/2`.

### `qEntropy_mul_log_eq_qaryEntropy` (2 declarations, 2 files)

- `theorem CodingTheory.qEntropy_mul_log_eq_qaryEntropy` [ArkLib/Data/CodingTheory/ProximityPrizeLeaves.lean:143](../../../ArkLib/Data/CodingTheory/ProximityPrizeLeaves.lean#L143) — **Base-change bridge for the `q`-ary entropy.** For `q ≥ 2`, ArkLib's `qEntropy` (defined with base-
- `theorem CodingTheory.qEntropy_mul_log_eq_qaryEntropy` [ArkLib/Data/CodingTheory/ProximityPrizeLeaves2.lean:82](../../../ArkLib/Data/CodingTheory/ProximityPrizeLeaves2.lean#L82) — **Base-change bridge for the `q`-ary entropy** (re-proven locally so that this file is self-containe

### `totalDegree_ehQ_le` (2 declarations, 2 files)

- `lemma MvPolynomial.totalDegree_ehQ_le` [ArkLib/ToMathlib/RestrictedSumset.lean:262](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L262) — `ehQ Cset` has total degree at most `\|Cset\| + 1`.
- `lemma MvPolynomial.totalDegree_ehQ_le` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:307](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L307) — `ehQ h Cset` has total degree at most `deg(vdmX) + \|Cset\|`.

### `totalDegree_prod_sub_pow_le` (2 declarations, 2 files)

- `lemma MvPolynomial.totalDegree_prod_sub_pow_le` [ArkLib/ToMathlib/RestrictedSumset.lean:178](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L178) — **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{\|s\|}` by a pol
- `lemma MvPolynomial.totalDegree_prod_sub_pow_le` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:186](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L186) — **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{\|s\|}` by a pol

### `uniform_event_mass` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:55](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L55) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly
- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:165](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L165) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly

## Near-duplicate docstrings (Jaccard ≥ 0.85, 116 cross-file pairs)

Each pair has docstrings sharing a high fraction of (4+-letter) words, in different files. Most are unrelated coincidences in boilerplate; look for pairs where the *concept* matches.

- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:908](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L908) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:994](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L994)
    - a: The Logic Instance for the final sumcheck step. This is a 1-message protocol where the prover sends 
    - b: The Logic Instance for the final sumcheck step. This is a 1-message protocol where the prover sends 
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:96](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L96) vs `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:171](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L171)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:96](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L96) vs `Binius.RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:86](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L86)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:96](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L96) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:96](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L96)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:68](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L68) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L140)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:68](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L68) vs `Binius.RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:74](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L74)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:68](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L68) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:84](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L84)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:111](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L111) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:191](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L191)
    - a: Perfect completeness for the full Binary Basefold protocol (reduction)
    - b: Perfect completeness for the full Binary Basefold protocol (reduction)
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:45](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L45) vs `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:114](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L114)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:45](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L45) vs `Binius.RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:56](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L56)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:45](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L45) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:60](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L60)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1081](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1081) vs `Binius.RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:423](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L423)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1081](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1081) vs `RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:437](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L437)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1287](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1287) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1454](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1454)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1287](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1287) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:940](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L940)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:646](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L646) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1256](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1256)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:646](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L646) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:770](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L770)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1107](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1107) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1270](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1270)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1107](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1107) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:863](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L863)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1590](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1590) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1650](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1650)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1590](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1590) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1122](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1122)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1298](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1298) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:943](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L943)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:171](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L171) vs `Binius.RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:86](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L86)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:171](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L171) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:96](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L96)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L140) vs `Binius.RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:74](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L74)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L140) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:84](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L84)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:114](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L114) vs `Binius.RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:56](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L56)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:114](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L114) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:60](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L60)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.RingSwitching.BatchingPhase.PrvState` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:319](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L319) vs `RingSwitching.BatchingPhase.PrvState` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:121](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L121)
    - a: The state maintained by the prover throughout the batching phase.
    - b: The state maintained by the prover throughout the batching phase.
- **1.00** `Binius.RingSwitching.BatchingPhase.batchingInputRelation` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:97](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L97) vs `RingSwitching.BatchingPhase.batchingInputRelation` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:300](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L300)
    - a: Input relation: the witness `t` and `t'` are consistent, and `t` satisfies the original claim.
    - b: Input relation: the witness `t` and `t'` are consistent, and `t` satisfies the original claim.
- **1.00** `Binius.RingSwitching.BatchingPhase.batchingKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:482](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L482) vs `RingSwitching.BatchingPhase.batchingKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:404](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L404)
    - a: Knowledge state function for the batching phase.
    - b: Knowledge state function for the batching phase.
- **1.00** `Binius.RingSwitching.BatchingPhase.batchingWitMid` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:408](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L408) vs `RingSwitching.BatchingPhase.batchingWitMid` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:305](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L305)
    - a: Intermediate witness types for RBR knowledge soundness.
    - b: Intermediate witness types for RBR knowledge soundness.
- **1.00** `Binius.RingSwitching.BatchingPhase.failureState` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:71](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L71) vs `RingSwitching.BatchingPhase.failureState` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:106](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L106)
    - a: A dummy state returned by the verifier upon failure of Check 1.
    - b: A dummy state returned by the verifier upon failure of Check 1.
- **1.00** `Binius.RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:86](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L86) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:96](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L96)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:74](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L74) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:84](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L84)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:56](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L56) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:60](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L60)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.RingSwitching.MLPEvalRelation` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:236](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L236) vs `RingSwitching.MLPEvalRelation` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:246](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L246)
    - a: Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation
    - b: Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation
- **1.00** `Binius.RingSwitching.MLPEvalStatement` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:203](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L203) vs `RingSwitching.MLPEvalStatement` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:207](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L207)
    - a: Initial input (input to the batching phase): a polynomial-evaluation claim `s = t(r)`.
    - b: Initial input (input to the Batching Phase): a polynomial-evaluation claim `s = t(r)`.
- **1.00** `Binius.RingSwitching.RingSwitching_SumcheckMultParam` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:381](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L381) vs `RingSwitching.RingSwitching_SumcheckMultParam` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:388](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L388)
    - a: Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier.
    - b: Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier.
- **1.00** `Binius.RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1711](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1711) vs `RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1225](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1225)
    - a: Large-field reduction: Sumcheck seqCompose, then append FinalSum
    - b: Large-field reduction: Sumcheck seqCompose, then append FinalSum
- **1.00** `Binius.RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1702](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1702) vs `RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1189](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1189)
    - a: Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum
    - b: Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum
- **1.00** `Binius.RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1799](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1799) vs `RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1309](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1309)
    - a: RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum)
    - b: RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum)
- **1.00** `Binius.RingSwitching.SumcheckPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1454](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1454) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:940](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L940)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1256](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1256) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:770](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L770)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1270](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1270) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:863](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L863)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1650](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1650) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1122](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1122)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:601](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L601) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:625](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L625)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.RingSwitching.SumcheckPhase.sumcheckLoopOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1681](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1681) vs `RingSwitching.SumcheckPhase.sumcheckLoopOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1162](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1162)
    - a: Composed oracle reduction for the SumcheckStep (seqCompose over ℓ')
    - b: Composed oracle reduction for the SumcheckStep (seqCompose over ℓ')
- **1.00** `Binius.RingSwitching.SumcheckPhase.sumcheckLoopOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1672](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1672) vs `RingSwitching.SumcheckPhase.sumcheckLoopOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1143](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1143)
    - a: Composed oracle verifier for the SumcheckStep (seqCompose over ℓ')
    - b: Composed oracle verifier for the SumcheckStep (seqCompose over ℓ')
- **1.00** `Binius.RingSwitching.TensorAlgebra` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:63](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L63) vs `RingSwitching.TensorAlgebra` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:62](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L62)
    - a: Tensor Algebra A = L ⊗_K L. Based on the spec, it's viewed as (2^κ)x(2^κ) arrays of K-elements. The 
    - b: Tensor Algebra A = L ⊗_K L. Based on the spec, it's viewed as (2^κ)x(2^κ) arrays of K-elements. The 
- **1.00** `Binius.RingSwitching.aeval_eqPolynomial_zeroOne` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:683](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L683) vs `RingSwitching.aeval_eqPolynomial_zeroOne` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:773](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L773)
    - a: `aeval` of `eqPolynomial` at a Boolean coefficient vector lands in `L₀` as `eqTilde`.
    - b: `aeval` of `eqPolynomial` at a Boolean coefficient vector lands in `L₀` as `eqTilde`.
- **1.00** `Binius.RingSwitching.aeval_eq_sum_eqTilde` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:700](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L700) vs `RingSwitching.aeval_eq_sum_eqTilde` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:790](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L790)
    - a: **MLE evaluation identity (through the algebra map).** For a multilinear `t` over `K₀`, its `L₀`-eva
    - b: **MLE evaluation identity (through the algebra map).** For a multilinear `t` over `K₀`, its `L₀`-eva
- **1.00** `Binius.RingSwitching.boolHypercubeEmb` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:889](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L889) vs `RingSwitching.boolHypercubeEmb` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1349](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1349)
    - a: The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → L₀)` induced by a 2-element domain embed
    - b: The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → L₀)` induced by a 2-element domain embed
- **1.00** `Binius.RingSwitching.boolHypercube_sum_eq` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:897](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L897) vs `RingSwitching.boolHypercube_sum_eq` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1357](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1357)
    - a: **`𝓑`-domain hypercube sum reindexes to the Boolean hypercube.** For any `𝓑 : Fin 2 ↪ L₀`, summing `
    - b: **`𝓑`-domain hypercube sum reindexes to the Boolean hypercube.** For any `𝓑 : Fin 2 ↪ L₀`, summing `
- **1.00** `Binius.RingSwitching.boolHypercube_sum_pinned` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:917](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L917) vs `RingSwitching.boolHypercube_sum_pinned` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1377](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1377)
    - a: **Pinned-`𝓑` Boolean-domain sumcheck sum.** When `𝓑` is pinned to the Boolean embedding (`𝓑 c = if c
    - b: **Pinned-`𝓑` Boolean-domain sumcheck sum.** When `𝓑` is pinned to the Boolean embedding (`𝓑 c = if c
- **1.00** `Binius.RingSwitching.check_rows_sum_eq_aeval` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:740](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L740) vs `RingSwitching.check_rows_sum_eq_aeval` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1207](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1207)
    - a: **DP24 ring-switching capstone (sum form).** The verifier's row-decomposition check sum, applied to 
    - b: **DP24 ring-switching capstone (sum form).** The verifier's row-decomposition check sum, applied to 
- **1.00** `Binius.RingSwitching.componentWise_φ₁_embed_MLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:171](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L171) vs `RingSwitching.componentWise_embed_MLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:170](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L170)
    - a: **Component-wise `φ₁` embedding**. Takes a polynomial `t'` with coefficients in `L` and embeds it in
    - b: **Component-wise `φ₁` embedding**. Takes a polynomial `t'` with coefficients in `L` and embeds it in
- **1.00** `Binius.RingSwitching.compute_A_MLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:370](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L370) vs `RingSwitching.compute_A_MLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:377](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L377)
    - a: Step 4b: P writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension of `A_func`.
    - b: Step 4b: P writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension of `A_func`.
- **1.00** `Binius.RingSwitching.compute_A_func` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:353](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L353) vs `RingSwitching.compute_A_func` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:360](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L360)
    - a: Step 4a: For each `w ∈ {0,1}^{ℓ'}`, P decompose `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})` `=: Σ_{
    - b: Step 4a: For each `w ∈ {0,1}^{ℓ'}`, P decompose `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})` `=: Σ_{
- **1.00** `Binius.RingSwitching.compute_final_eq_value` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:411](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L411) vs `RingSwitching.compute_final_eq_value` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:419](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L419)
    - a: Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`, where e_u is the row compone
    - b: Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`, where e_u is the row compone
- **1.00** `Binius.RingSwitching.compute_s0` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:394](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L394) vs `RingSwitching.compute_s0` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:402](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L402)
    - a: Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`, where ŝ_u is the row components o
    - b: Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`, where ŝ_u is the row components o
- **1.00** `Binius.RingSwitching.decompose_rows_packMLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:598](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L598) vs `RingSwitching.decompose_rows_packMLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1186](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1186)
    - a: **Row recovery of `t`-evaluations.** The row components of the prover's tensor `ŝ = embedded_MLP_eva
    - b: **Row recovery of `t`-evaluations.** The row components of the prover's tensor `ŝ = embedded_MLP_eva
- **1.00** `Binius.RingSwitching.decompose_rows_sum` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:552](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L552) vs `RingSwitching.decompose_rows_sum` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:668](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L668)
    - a: `decompose_tensor_algebra_rows` is additive over finite sums of tensors.
    - b: `decompose_tensor_algebra_rows` is additive over finite sums of tensors.
- **1.00** `Binius.RingSwitching.decompose_rows_φ₀φ₁` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:562](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L562) vs `RingSwitching.decompose_rows_φ₀φ₁` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:678](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L678)
    - a: Row decomposition of a separated tensor `φ₀(a) · φ₁(b) = a ⊗ b`: the `u`-th row component represents
    - b: Row decomposition of a separated tensor `φ₀(a) · φ₁(b) = a ⊗ b`: the `u`-th row component represents
- **1.00** `Binius.RingSwitching.decompose_tensor_algebra_columns` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:100](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L100) vs `RingSwitching.decompose_tensor_algebra_columns` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:99](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L99)
    - a: Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v)`. This views `L ⊗ L` as a mod
    - b: Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v)`. This views `L ⊗ L` as a mod
- **1.00** `Binius.RingSwitching.decompose_tensor_algebra_rows` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:92](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L92) vs `RingSwitching.decompose_tensor_algebra_rows` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:91](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L91)
    - a: Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u)`. This views `L ⊗ L` as a module
    - b: Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u)`. This views `L ⊗ L` as a module
- **1.00** `Binius.RingSwitching.embedded_MLP_eval_eq_sum` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:523](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L523) vs `RingSwitching.embedded_MLP_eval_eq_sum` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1150](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1150)
    - a: **DP24 packing expansion.** The prover's tensor `ŝ := φ₁(t')(φ₀(r_κ), …, φ₀(r_{ℓ-1}))` expands over 
    - b: **DP24 packing expansion.** The prover's tensor `ŝ := φ₁(t')(φ₀(r_κ), …, φ₀(r_{ℓ-1}))` expands over 
- **1.00** `Binius.RingSwitching.eqPoly_collapse` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:508](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L508) vs `RingSwitching.eqPoly_collapse` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:655](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L655)
    - a: The full `eqPolynomial` collapses through the mixed embedding to `φ₀` of its ordinary evaluation, by
    - b: The full `eqPolynomial` collapses through the mixed embedding to `φ₀` of its ordinary evaluation, by
- **1.00** `Binius.RingSwitching.eqTilde_concat_split` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:665](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L665) vs `RingSwitching.eqTilde_concat_split` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:756](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L756)
    - a: `eqTilde` of concatenated Boolean / point data factors along the κ/ℓ' split: `eqTilde (concat fp fs)
    - b: `eqTilde` of concatenated Boolean / point data factors along the κ/ℓ' split: `eqTilde (concat fp fs)
- **1.00** `Binius.RingSwitching.eqTilde_prod` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:616](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L616) vs `RingSwitching.eqTilde_prod` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:708](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L708)
    - a: `eqTilde` written as a product over coordinates of the symmetric Boolean factor.
    - b: `eqTilde` written as a product over coordinates of the symmetric Boolean factor.
- **1.00** `Binius.RingSwitching.hypercubeSplitEquiv` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:715](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L715) vs `RingSwitching.hypercubeSplitEquiv` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:805](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L805)
    - a: The κ-then-ℓ' hypercube concatenation `concatBit v w i = v i` for `i < κ`, `= w (i - κ)` otherwise —
    - b: The κ-then-ℓ' hypercube concatenation `concatBit v w i = v i` for `i < κ`, `= w (i - κ)` otherwise —
- **1.00** `Binius.RingSwitching.packMLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:114](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L114) vs `RingSwitching.packMLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:113](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L113)
    - a: **Definition 2.1 (MLE packing)**. Packs a small-field multilinear `t` into a large-field multilinear
    - b: **Definition 2.1 (MLE packing)**. Packs a small-field multilinear `t` into a large-field multilinear
- **1.00** `Binius.RingSwitching.packMLE_repr_eval` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:575](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L575) vs `RingSwitching.packMLE_repr_eval` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:691](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L691)
    - a: The basis coordinate of a packed evaluation recovers the small-field coefficient: `β.repr (t'(w)) u 
    - b: The basis coordinate of a packed evaluation recovers the small-field coefficient: `β.repr (t'(w)) u 
- **1.00** `Binius.RingSwitching.performCheckOriginalEvaluation_packMLE_iff` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:805](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L805) vs `RingSwitching.performCheckOriginalEvaluation_packMLE_iff_binaryTower` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1264](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1264)
    - a: **DP24 ring-switching capstone (decision form).** The verifier's Step-2 check on the prover's honest
    - b: **DP24 ring-switching capstone (decision form).** The verifier's Step-2 check on the prover's honest
- **1.00** `Binius.RingSwitching.prod_concat_split` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:627](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L627) vs `RingSwitching.prod_concat_split` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:719](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L719)
    - a: A product over `Fin (ℓ' + κ₀)` of a function defined by the κ/ℓ'-dichotomy splits as the product of 
    - b: A product over `Fin (ℓ' + κ₀)` of a function defined by the κ/ℓ'-dichotomy splits as the product of 
- **1.00** `Binius.RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:953](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L953) vs `RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1414](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1414)
    - a: **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
    - b: **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
- **1.00** `Binius.RingSwitching.simulateQ_simOracle2_query` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:975](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L975) vs `RingSwitching.simulateQ_simOracle2_query` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1436](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1436)
    - a: **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as `simulateQ_s
    - b: **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as `simulateQ_s
- **1.00** `Binius.RingSwitching.singleEq_collapse` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:491](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L491) vs `RingSwitching.singleEq_collapse` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:638](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L638)
    - a: A single `eqPolynomial` factor, evaluated through the mixed embedding `eval₂ φ₁ (φ₀ ∘ g)` at a Boole
    - b: A single `eqPolynomial` factor, evaluated through the mixed embedding `eval₂ φ₁ (φ₀ ∘ g)` at a Boole
- **1.00** `Binius.RingSwitching.sumcheckRoundRelation` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:447](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L447) vs `RingSwitching.sumcheckRoundRelation` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:461](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L461)
    - a: Input relation for single round: proper sumcheck statement
    - b: Input relation for single round: proper sumcheck statement
- **1.00** `Binius.RingSwitching.sumcheckSum_X0_eq` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:849](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L849) vs `RingSwitching.sumcheckSum_X0_eq` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1309](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1309)
    - a: **Sumcheck hypercube sum depends on the evaluation domain `𝓑`.** The single-variable sumcheck consis
    - b: **Sumcheck hypercube sum depends on the evaluation domain `𝓑`.** The single-variable sumcheck consis


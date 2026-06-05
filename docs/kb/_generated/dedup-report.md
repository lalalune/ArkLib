# ArkLib dedup-candidate report

Generated from `docs/kb/_generated/declarations.json`. **Eyeball, do not auto-rewrite.** The point is to surface name collisions and doc-string overlap that *might* indicate an opportunity to consolidate.

## Stats

- `ArkLib` — 289 files, 5588 declarations

## Same short-name across multiple files (150 groups)

Each group lists declarations sharing a short name across ≥2 files. Most are legitimate (overloaded interface, paper-shape vs general form), but the list is the right anchor to look for duplicates.

### `reduction` (12 declarations, 11 files)

- `def KZG.CommitmentScheme.reduction` [ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean:115](../../../ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean#L115) — The reduction breaking ARSDH using a successful function-binding adversary. The reduction follows th
- `def CheckClaim.reduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:55](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L55) — The reduction for the `CheckClaim` reduction.
- `def DoNothing.reduction` [ArkLib/ProofSystem/Component/DoNothing.lean:43](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L43) — The reduction for the `DoNothing` reduction. - Prover simply returns the statement and witness. - Ve
- `def NoInteraction.reduction` [ArkLib/ProofSystem/Component/NoInteraction.lean:62](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L62) — The no-interaction reduction can be specified by a tuple of functions: - `mapStmt : StmtIn → OracleC
- `def ReduceClaim.reduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:56](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L56) — The reduction for the `ReduceClaim` reduction.
- `def SendWitness.reduction` [ArkLib/ProofSystem/Component/SendWitness.lean:61](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L61) — (no docstring)
- `def Fri.Spec.reduction` [ArkLib/ProofSystem/Fri/Spec/General.lean:98](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L98) — (no docstring)
- `def Sumcheck.Spec.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:168](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L168) — The sum-check protocol as a reduction
- `def Sumcheck.Spec.SingleRound.Simple.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:496](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L496) — The reduction for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1120](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1120) — The sum-check reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Spec.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:350](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L350) — Honest reduction for Construction 6.2: the package `{prover, verifier}` over the bundled-input `Redu
- `def ToyProblem.SimplifiedIOR.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:165](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L165) — Honest reduction for Construction 6.9.

### `pSpec` (12 declarations, 10 files)

- `def RandomQuery.pSpec` [ArkLib/ProofSystem/Component/RandomQuery.lean:53](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L53) — (no docstring)
- `def SendClaim.pSpec` [ArkLib/ProofSystem/Component/SendClaim.lean:31](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L31) — (no docstring)
- `def SendWitness.pSpec` [ArkLib/ProofSystem/Component/SendWitness.lean:39](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L39) — (no docstring)
- `def Fri.Spec.FoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:338](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L338) — Each round of the FRI protocol begins with the verifier sending a random field element as the challe
- `def Fri.Spec.FinalFoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:582](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L582) — The final folding round of the FRI protocol begins with the verifier sending a random field element 
- `def Fri.Spec.QueryRound.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:757](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L757) — (no docstring)
- `def Logup.pSpec` [ArkLib/ProofSystem/Logup/Protocol.lean:75](../../../ArkLib/ProofSystem/Logup/Protocol.lean#L75) — Protocol 2 transcript shape: the outer LogUp messages followed by ArkLib's generic sumcheck.
- `def StirIOP.Round.pSpec` [ArkLib/ProofSystem/Stir/RoundProtocol.lean:60](../../../ArkLib/ProofSystem/Stir/RoundProtocol.lean#L60) — The protocol spec of one STIR fold round: the verifier first sends a folding challenge in `F` (`V_to
- `def Sumcheck.Spec.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:125](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L125) — The protocol specification for the general sum-check protocol, which is the composition of the singl
- `def Sumcheck.Spec.SingleRound.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:147](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L147) — The protocol specification for a single round of sum-check. Has the form `⟨!v[.P_to_V, .V_to_P], !v[
- `def ToyProblem.Spec.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:121](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L121) — Protocol specification for Construction 6.2: three rounds, in the order V → P  (γ : F)            --
- `def ToyProblem.SimplifiedIOR.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:105](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L105) — Protocol specification for Construction 6.9: a single `V → P` round sending the combination randomne

### `oracleVerifier` (11 declarations, 10 files)

- `def CheckClaim.oracleVerifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:197](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L197) — The oracle verifier for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleVerifier` [ArkLib/ProofSystem/Component/DoNothing.lean:72](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L72) — The oracle verifier for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleVerifier` [ArkLib/ProofSystem/Component/RandomQuery.lean:82](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L82) — The oracle verifier simply returns the challenge, and performs no checks.
- `def ReduceClaim.oracleVerifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:198](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L198) — The oracle verifier for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleVerifier` [ArkLib/ProofSystem/Component/SendClaim.lean:63](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L63) — The verifier checks that the relationship `rel oldStmt newStmt` holds. It has access to the original
- `def SendSingleWitness.oracleVerifier` [ArkLib/ProofSystem/Component/SendWitness.lean:237](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L237) — The oracle verifier for the `SendSingleWitness` oracle reduction. The verifier receives the input st
- `def RingSwitching.BatchingPhase.oracleVerifier` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:143](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L143) — (no docstring)
- `def Sumcheck.Spec.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:158](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L158) — The oracle verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:556](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L556) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1115](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1115) — The oracle verifier for the `i`-th round of the sum-check protocol
- `def ToyProblem.Spec.oracleVerifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:427](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L427) — Oracle verifier for Construction 6.2. Queries the prover's message `g` once and the two oracle codew

### `oracleReduction` (11 declarations, 9 files)

- `def CheckClaim.oracleReduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:205](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L205) — The oracle reduction for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleReduction` [ArkLib/ProofSystem/Component/DoNothing.lean:82](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L82) — The oracle reduction for the `DoNothing` oracle reduction. - Prover simply returns the (non-oracle a
- `def RandomQuery.oracleReduction` [ArkLib/ProofSystem/Component/RandomQuery.lean:100](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L100) — Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction: the input o
- `def ReduceClaim.oracleReduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:215](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L215) — The oracle reduction for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleReduction` [ArkLib/ProofSystem/Component/SendClaim.lean:92](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L92) — Combine the prover and verifier into an oracle reduction. The input has no statement or witness, but
- `def SendSingleWitness.oracleReduction` [ArkLib/ProofSystem/Component/SendWitness.lean:250](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L250) — (no docstring)
- `def Sumcheck.Spec.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:180](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L180) — The sum-check protocol as an oracle reduction
- `def Sumcheck.Spec.SingleRound.Simpler.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:383](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L383) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:575](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L575) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1126](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1126) — The sum-check oracle reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Spec.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:459](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L459) — Honest oracle reduction for Construction 6.2: the `OracleProver` / `OracleVerifier` pair packaged as

### `verifier` (11 declarations, 9 files)

- `def CheckClaim.verifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:50](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L50) — The verifier for the `CheckClaim` reduction.
- `def DoNothing.verifier` [ArkLib/ProofSystem/Component/DoNothing.lean:34](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L34) — The verifier for the `DoNothing` reduction.
- `def NoInteraction.verifier` [ArkLib/ProofSystem/Component/NoInteraction.lean:53](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L53) — The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a function
- `def ReduceClaim.verifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:52](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L52) — The verifier for the `ReduceClaim` reduction.
- `def SendWitness.verifier` [ArkLib/ProofSystem/Component/SendWitness.lean:57](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L57) — (no docstring)
- `def Sumcheck.Spec.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L149) — The verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:487](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L487) — The verifier for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1109](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1109) — The verifier for the `i`-th round of the sum-check protocol
- `def Sumcheck.Spec.SingleRound.Unfolded.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1662](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1662) — The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1`
- `def ToyProblem.Spec.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:336](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L336) — Honest verifier for Construction 6.2. Takes the bundled input `(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂
- `def ToyProblem.SimplifiedIOR.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:154](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L154) — Honest verifier for Construction 6.9. Reads `γ` from the transcript and produces the new statement `

### `OracleStatement` (9 declarations, 9 files)

- `def BatchedFri.Spec.OracleStatement` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:40](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L40) — An oracle for each batched polynomial.
- `def Binius.BinaryBasefold.OracleStatement` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:488](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L488) — For the `i`-th round of the protocol, there will be oracle statements corresponding to all committed
- `def R1CS.OracleStatement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:48](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L48) — (no docstring)
- `def Fri.Spec.OracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:88](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L88) — For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the beginning
- `abbrev Spartan.Spec.OracleStatement` [ArkLib/ProofSystem/Spartan/Basic.lean:144](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L144) — This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R`
- `def StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:81](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L81) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- `def Sumcheck.Spec.OracleStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:134](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L134) — Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of individual 
- `def ToyProblem.Spec.OracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:88](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L88) — Oracle statements of Construction 6.2: the two purported codewords `f₁, f₂ : ι → F`. The verifier on
- `def WhirIOP.OracleStatement` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:146](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L146) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type

### `oracleProver` (9 declarations, 8 files)

- `def CheckClaim.oracleProver` [ArkLib/ProofSystem/Component/CheckClaim.lean:184](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L184) — The oracle prover for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleProver` [ArkLib/ProofSystem/Component/DoNothing.lean:67](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L67) — The oracle prover for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleProver` [ArkLib/ProofSystem/Component/RandomQuery.lean:62](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L62) — The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`, a
- `def ReduceClaim.oracleProver` [ArkLib/ProofSystem/Component/ReduceClaim.lean:188](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L188) — The oracle prover for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleProver` [ArkLib/ProofSystem/Component/SendClaim.lean:36](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L36) — The prover takes in the old oracle statement as input, and sends it as the protocol message.
- `def SendWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:133](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L133) — The oracle prover for the `SendWitness` oracle reduction. For each round `i : Fin (FinEnum.card ιw)`
- `def SendSingleWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:221](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L221) — The oracle prover for the `SendSingleWitness` oracle reduction. The prover sends the witness `wit` t
- `def RingSwitching.BatchingPhase.oracleProver` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:95](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L95) — (no docstring)
- `def ToyProblem.Spec.oracleProver` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:379](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L379) — Same as `prover` but exposed at the `OracleProver` signature. The underlying `Prover` is identical (

### `prover` (9 declarations, 8 files)

- `def CheckClaim.prover` [ArkLib/ProofSystem/Component/CheckClaim.lean:39](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L39) — The prover for the `CheckClaim` reduction.
- `def DoNothing.prover` [ArkLib/ProofSystem/Component/DoNothing.lean:30](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L30) — The prover for the `DoNothing` reduction.
- `def NoInteraction.prover` [ArkLib/ProofSystem/Component/NoInteraction.lean:43](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L43) — The prover in a no-interaction reduction can be specified by a tuple of functions: - `mapStmt : Stmt
- `def ReduceClaim.prover` [ArkLib/ProofSystem/Component/ReduceClaim.lean:44](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L44) — The prover for the `ReduceClaim` reduction.
- `def SendWitness.prover` [ArkLib/ProofSystem/Component/SendWitness.lean:47](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L47) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:465](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L465) — The prover in the simple description of a single round of sum-check. Takes in input `target : R` and
- `def Sumcheck.Spec.SingleRound.Unfolded.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1652](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1652) — The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only well-
- `def ToyProblem.Spec.prover` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:292](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L292) — Honest prover for Construction 6.2. After receiving the combination randomness `γ`, the prover sends
- `def ToyProblem.SimplifiedIOR.prover` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:123](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L123) — Honest prover for Construction 6.9. After receiving `γ`, sets the new witness `M_new := M₀ + γ·M₁` a

### `relation` (9 declarations, 8 files)

- `def ArkLib.Lattices.ModuleSIS.relation` [ArkLib/Data/Lattices/ModuleSIS.lean:81](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L81) — The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short, and lies in the k
- `def ConstraintSystem.relation` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:68](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L68) — The underlying set-theoretic relation at a given index.
- `def Lookup.relation` [ArkLib/ProofSystem/ConstraintSystem/Lookup.lean:25](../../../ArkLib/ProofSystem/ConstraintSystem/Lookup.lean#L25) — The lookup relation. Takes in a collection of values and a table, both containers for elements of ty
- `def MemoryChecking.ReadOnly.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:128](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L128) — The read-only memory checking relation. It takes a memory `mem` and a list of read operations `ops`.
- `def MemoryChecking.ReadWrite.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:161](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L161) — The read-write memory checking relation. It takes an initial memory `startMem`, a final memory `fina
- `def Plonk.relation` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:193](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L193) — To define a relation based on the constraint system, we extend it with: - A natural number `ℓ ≤ m` r
- `def R1CS.relation` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:61](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L61) — The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean component-wise 
- `abbrev Spartan.Spec.relation` [ArkLib/ProofSystem/Spartan/Basic.lean:152](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L152) — This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨`
- `def ToyProblem.relation` [ArkLib/ProofSystem/ToyProblem/Definitions.lean:74](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean#L74) — **Definition 6.1 of [ABF26]** (toy problem relation `R_C^ℓ`). Given a base code `C ⊆ (ι → F)` (the p

### `inputRelation` (10 declarations, 7 files)

- `def BatchedFri.Spec.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/General.lean:41](../../../ArkLib/ProofSystem/BatchedFri/Spec/General.lean#L41) — (no docstring)
- `def BatchedFri.Spec.BatchingRound.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:56](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L56) — (no docstring)
- `def Fri.Spec.inputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:37](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L37) — (no docstring)
- `def Fri.Spec.FoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:273](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L273) — The FRI non-final folding round input relation, with proximity parameter `0 < δ`, for the `i`-th rou
- `def Fri.Spec.FinalFoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:521](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L521) — Input relation for the final folding round, with proximity parameter `0 < δ`. The round-`k` codeword
- `def Fri.Spec.QueryRound.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:736](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L736) — (no docstring)
- `def Logup.inputRelation` [ArkLib/ProofSystem/Logup/Common.lean:162](../../../ArkLib/ProofSystem/Logup/Common.lean#L162) — Semantic input relation for Protocol 2: every lookup-column value occurs in the table range.
- `def Sumcheck.Spec.SingleRound.Simpler.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:325](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L325) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:450](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L450) — (no docstring)
- `def ToyProblem.Spec.inputRelation` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:176](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L176) — The IOR-shaped input relation derived from `ToyProblem.relation` (Definition 6.1). `((v, μ₁, μ₂), (f

### `outputRelation` (10 declarations, 7 files)

- `def BatchedFri.Spec.BatchingRound.outputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:65](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L65) — (no docstring)
- `def Fri.Spec.outputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:47](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L47) — (no docstring)
- `def Fri.Spec.FoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:301](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L301) — The FRI non-final folding round output relation, with proximity parameter `0 < δ`, for the `i`-th ro
- `def Fri.Spec.FinalFoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:550](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L550) — Output relation for the final folding round. After the final round the prover sends a polynomial in 
- `def Fri.Spec.QueryRound.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:744](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L744) — (no docstring)
- `def Logup.outputRelation` [ArkLib/ProofSystem/Logup/Common.lean:189](../../../ArkLib/ProofSystem/Logup/Common.lean#L189) — The full protocol has a trivial final relation: successful verification returns `Unit`.
- `def Sumcheck.Spec.SingleRound.Simpler.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:354](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L354) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:453](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L453) — (no docstring)
- `def ToyProblem.Spec.outputRelation` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:255](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L255) — The IOR-shaped *relaxed* output relation derived from `ToyProblem.relaxedRelation` (Definition 6.3).
- `def ToyProblem.SimplifiedIOR.outputRelation` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:92](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L92) — The 1-arity relaxed relation `R̃¹_{C,δ}` — the output relation of Construction 6.9. Bundles the post

### `Witness` (6 declarations, 6 files)

- `def BatchedFri.Spec.Witness` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:48](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L48) — The Batched FRI protocol has as witness for each batched polynomial that is supposed to correspond t
- `structure Binius.BinaryBasefold.Witness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:509](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L509) — The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and `Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁'
- `def R1CS.Witness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:51](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L51) — (no docstring)
- `def Fri.Spec.Witness` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:109](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L109) — The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in the
- `abbrev Spartan.Spec.Witness` [ArkLib/ProofSystem/Spartan/Basic.lean:148](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L148) — This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R`
- `def ToyProblem.Spec.Witness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:96](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L96) — Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose encodings are the oracle codeword

### `oracleVerifier_rbrKnowledgeSoundness` (7 declarations, 5 files)

- `theorem DoNothing.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:98](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L98) — The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound.
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomQuery.lean:275](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L275) — The `RandomQuery` oracle reduction is round-by-round knowledge sound. The key fact governing the sou
- `theorem ReduceClaim.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:331](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L331) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:218](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L218) — Round-by-round knowledge soundness with error `deg / \|R\|` per challenge for the (full) sum-check pro
- `theorem Sumcheck.Spec.SingleRound.Simpler.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:421](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L421) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1037](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1037) — Round-by-round knowledge soundness for the oracle verifier
- `theorem Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1547](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1547) — Round-by-round knowledge soundness theorem for single-round of sum-check, obtained by transporting t

### `Statement` (5 declarations, 5 files)

- `def R1CS.Statement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:45](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L45) — (no docstring)
- `def Fri.Spec.Statement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:79](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L79) — For the `i`-th round of the protocol, the input statement is equal to the challenges sent from round
- `abbrev Spartan.Spec.Statement` [ArkLib/ProofSystem/Spartan/Basic.lean:140](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L140) — This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R`
- `structure Sumcheck.Structured.Statement` [ArkLib/ProofSystem/Sumcheck/Structured.lean:197](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L197) — Statement per iterated sumcheck round
- `def ToyProblem.Spec.Statement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:82](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L82) — Input (explicit) statement of Construction 6.2: the linear-constraint vector `v ∈ F^k` and the two c

### `StmtIn` (5 declarations, 4 files)

- `def RandomQuery.StmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:30](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L30) — (no docstring)
- `structure Logup.StmtIn` [ArkLib/ProofSystem/Logup/Common.lean:131](../../../ArkLib/ProofSystem/Logup/Common.lean#L131) — Public parameter assumptions for Protocol 2. The paper fixes a finite field with characteristic larg
- `def Sumcheck.Spec.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:137](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L137) — The input statement for the (full) sum-check protocol, which contains only the target sum value
- `def Sumcheck.Spec.SingleRound.Simpler.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:322](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L322) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:439](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L439) — (no docstring)

### `disagreementSet` (4 declarations, 4 files)

- `def disagreementSet` [ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean#L63) — The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁. Specialisation of the canonical `Code.disagr
- `def Binius.BinaryBasefold.disagreementSet` [ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean:1781](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean#L1781) — Disagreement set Δ : The set of points where two functions disagree. For functions f^(i+ϑ) and g^(i+
- `def Quotienting.disagreementSet` [ArkLib/ProofSystem/Stir/Quotienting.lean:109](../../../ArkLib/ProofSystem/Stir/Quotienting.lean#L109) — We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S such that 
- `def BlockRelDistance.disagreementSet` [ArkLib/ProofSystem/Whir/BlockRelDistance.lean:104](../../../ArkLib/ProofSystem/Whir/BlockRelDistance.lean#L104) — Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then the (i,k)

### `reduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:70](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L70) — The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the input
- `theorem NoInteraction.reduction_completeness` [ArkLib/ProofSystem/Component/NoInteraction.lean:93](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L93) — Completeness of a no-interaction reduction. **Faithfulness of the hypothesis `hRel`.** `Reduction.ru
- `theorem ReduceClaim.reduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:66](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L66) — The `ReduceClaim` reduction satisfies perfect completeness for any relation.
- `theorem SendWitness.reduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:86](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L86) — The `SendWitness` reduction satisfies perfect completeness.

### `oracleReduction_perfectCompleteness` (5 declarations, 3 files)

- `theorem DoNothing.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:92](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L92) — The `DoNothing` oracle reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.SingleRound.Simpler.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:395](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L395) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:898](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L898) — Perfect completeness for the oracle reduction
- `theorem Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1534](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1534) — Completeness theorem for single-round of sum-check, obtained by transporting the completeness proof 
- `theorem ToyProblem.Spec.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:796](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L796) — **Honest completeness for Construction 6.2** (protocol-level form). The honest oracle reduction is p

### `ratchet` (5 declarations, 3 files)

- `def DomainSeparator.ratchet` [ArkLib/Data/Hash/DomainSep.lean:221](../../../ArkLib/Data/Hash/DomainSep.lean#L221) — Ratchet the state. Rust interface: ```rust pub fn ratchet(self) -> Self ```
- `def DuplexSponge.ratchet` [ArkLib/Data/Hash/DuplexSponge.lean:612](../../../ArkLib/Data/Hash/DuplexSponge.lean#L612) — ### Ratchet the sponge state for domain separation Algorithm (from Rust implementation): 1. Permute 
- `def HashStateWithInstructions.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:189](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L189) — Perform a ratchet operation. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainS
- `def FSVerifierState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:311](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L311) — Signal the end of statement with ratcheting. Rust interface: ```rust pub fn ratchet(&mut self) -> Re
- `def FSProverState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:424](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L424) — Ratchet the protocol state. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainSe

### `Adversary` (4 declarations, 3 files)

- `def AGM.Adversary` [ArkLib/AGM/Basic.lean:149](../../../ArkLib/AGM/Basic.lean#L149) — An adversary in the Algebraic Group Model (AGM) is defined as follows: - It is given knowledge of th
- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.Adversary` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:92](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L92) — A weak-binding adversary outputs two weak openings for the same commitment.
- `abbrev ArkLib.Lattices.SIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:53](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L53) — A search adversary for a SIS-style problem.
- `abbrev ArkLib.Lattices.ModuleSIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:96](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L96) — A Module-SIS adversary.

### `OStmtIn` (4 declarations, 3 files)

- `def RandomQuery.OStmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:33](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L33) — (no docstring)
- `def Logup.OStmtIn` [ArkLib/ProofSystem/Logup/Common.lean:139](../../../ArkLib/ProofSystem/Logup/Common.lean#L139) — Input oracle statements: the table `t` and lookup columns `fᵢ`, as multilinear oracles.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:323](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L323) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:445](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L445) — (no docstring)

### `OStmtOut` (4 declarations, 3 files)

- `def RandomQuery.OStmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:34](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L34) — (no docstring)
- `def Logup.OStmtOut` [ArkLib/ProofSystem/Logup/Common.lean:180](../../../ArkLib/ProofSystem/Logup/Common.lean#L180) — Output oracle statements for the full LogUp protocol.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:352](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L352) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:448](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L448) — (no docstring)

### `StmtOut` (4 declarations, 3 files)

- `def RandomQuery.StmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:31](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L31) — (no docstring)
- `def Logup.StmtOut` [ArkLib/ProofSystem/Logup/Common.lean:170](../../../ArkLib/ProofSystem/Logup/Common.lean#L170) — The full LogUp protocol returns no additional public data on success.
- `def Sumcheck.Spec.SingleRound.Simpler.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:351](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L351) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:442](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L442) — (no docstring)

### `drop` (4 declarations, 3 files)

- `def Fin.drop` [ArkLib/Data/Fin/Tuple/Defs.lean:60](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L60) — Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.
- `def ProtocolSpec.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:117](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L117) — Drop the first `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:174](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L174) — (no docstring)
- `def SumcheckDomain.drop` [ArkLib/ProofSystem/Sumcheck/Domain.lean:133](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L133) — Drop the first `j` coordinates, leaving the domain on the remaining `k - j` coordinates: coordinate 

### `reduction_perfectCompleteness` (4 declarations, 3 files)

- `theorem DoNothing.reduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:51](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L51) — The `DoNothing` reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:208](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L208) — Perfect completeness for the (full) sum-check protocol
- `theorem Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:609](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L609) — Perfect completeness for the (non-oracle) reduction
- `theorem Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1516](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1516) — (no docstring)

### `toFinset` (4 declarations, 3 files)

- `def ReedSolomon.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon.lean:81](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L81) — (no docstring)
- `def Domain.CosetFftDomainClass.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:229](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L229) — (no docstring)
- `abbrev Domain.CosetFftDomain.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:245](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L245) — (no docstring)
- `abbrev Domain.FftDomain.toFinset` [ArkLib/Data/Domain/FftDomain/Defs.lean:114](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L114) — (no docstring)

### `verifier_rbrKnowledgeSoundness` (4 declarations, 3 files)

- `theorem DoNothing.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:57](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L57) — The `DoNothing` verifier is perfectly round-by-round knowledge sound.
- `theorem ReduceClaim.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:169](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L169) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1031](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1031) — Round-by-round knowledge soundness for the verifier
- `theorem Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1524](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1524) — (no docstring)

### `Message` (3 declarations, 3 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Message` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:122](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L122) — Messages: block vectors over the message row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Message` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:32](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L32) — Messages: column vectors over `Rq Φ`.
- `def ProtocolSpec.Message` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:66](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L66) — The type of the `i`-th message in a protocol specification. This does not distinguish between messag

### `Opening` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.Opening` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:98](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L98) — A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)` (`Decomp`) ext
- `abbrev ArkLib.Lattices.Ajtai.Simple.Opening` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:43](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L43) — The simple Ajtai commitment has no auxiliary opening data.
- `structure Commitment.Opening` [ArkLib/CommitmentScheme/Basic.lean:59](../../../ArkLib/CommitmentScheme/Basic.lean#L59) — The opening protocol used to prove a claimed oracle response for committed data.

### `OutputStatement` (3 declarations, 3 files)

- `abbrev Sumcheck.Spec.OutputStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:129](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L129) — (no docstring)
- `def ToyProblem.Spec.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:101](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L101) — Output statement: the IOR is a yes/no test — accept (return `()`) or short-circuit to `none` via `Op
- `def ToyProblem.SimplifiedIOR.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:71](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L71) — Output statement for C6.9: the new `(v, μ_new)` pair. The constraint count drops from 2 to 1 (a sing

### `Params` (3 declarations, 3 files)

- `structure Poseidon2.Params` [ArkLib/Data/Hash/Poseidon2.lean:412](../../../ArkLib/Data/Hash/Poseidon2.lean#L412) — The parameters determining a Poseidon2 permutation (over the KoalaBear field)
- `structure StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:32](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L32) — **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun
- `structure WhirIOP.Params` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:54](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L54) — ** Per‑round protocol parameters. ** For a fixed depth `M`, the reduction runs `M + 1` rounds. In ro

### `PublicParams` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.PublicParams` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:77](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L77) — Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`.
- `abbrev ArkLib.Lattices.Ajtai.Simple.PublicParams` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:29](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L29) — Public parameters: the Ajtai matrix `A`.
- `structure Spartan.PublicParams` [ArkLib/ProofSystem/Spartan/Basic.lean:110](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L110) — The public parameters of the (padded) Spartan protocol. Consists of the number of bits of the R1CS d

### `absorb` (3 declarations, 3 files)

- `def DomainSeparator.absorb` [ArkLib/Data/Hash/DomainSep.lean:182](../../../ArkLib/Data/Hash/DomainSep.lean#L182) — Absorb `count` native elements. Rust interface: ```rust pub fn absorb(self, count: usize, label: &st
- `def DuplexSponge.absorb` [ArkLib/Data/Hash/DuplexSponge.lean:416](../../../ArkLib/Data/Hash/DuplexSponge.lean#L416) — ### Absorb a list of units into the sponge (paper version) Paper algorithm (process one element at a
- `def HashStateWithInstructions.absorb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:109](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L109) — Perform secure absorption of elements into the sponge. Rust interface: ```rust pub fn absorb(&mut se

### `commit` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.Simple.commit` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:38](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L38) — Deterministically commit by multiplying the public matrix by the message vector.
- `def KZG.commit` [ArkLib/CommitmentScheme/KZG/Basic.lean:55](../../../ArkLib/CommitmentScheme/KZG/Basic.lean#L55) — To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of maximum deg
- `def SimpleRO.commit` [ArkLib/CommitmentScheme/SimpleRO.lean:43](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L43) — (no docstring)

### `commitmentScheme` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commitmentScheme` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:200](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L200) — The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound weak ver
- `def ArkLib.Lattices.Ajtai.Simple.commitmentScheme` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:56](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L56) — The simple Ajtai commitment as a `CommitmentScheme`. An opening is accepted only when the message sa
- `def SimpleRO.commitmentScheme` [ArkLib/CommitmentScheme/SimpleRO.lean:83](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L83) — (no docstring)

### `coreInteractionOracleReduction` (3 declarations, 3 files)

- `def coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:610](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L610) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:764](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L764) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1268](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1268) — Large-field reduction: Sumcheck seqCompose, then append FinalSum

### `coreInteractionOracleVerifier` (3 declarations, 3 files)

- `def coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:595](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L595) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:746](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L746) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1259](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1259) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum

### `finalSumcheckKStateProp` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1010](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1010) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:653](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L653) — (no docstring)
- `def RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1054](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1054) — (no docstring)

### `finalSumcheckKnowledgeStateFunction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1044](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1044) — The knowledge state function for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:695](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L695) — The knowledge state function for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1091](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1091) — The knowledge state function for the final sumcheck step

### `finalSumcheckOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:939](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L939) — The oracle reduction for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:571](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L571) — The oracle reduction for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:867](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L867) — The oracle reduction for the final sumcheck step

### `finalSumcheckOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:953](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L953) — Perfect completeness for the final sumcheck step
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:587](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L587) — Perfect completeness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:960](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L960) — Perfect completeness for the final sumcheck step

### `finalSumcheckOracleVerifier_rbrKnowledgeSoundness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1064](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1064) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:724](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L724) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1212](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1212) — Round-by-round knowledge soundness for the final sumcheck step

### `finalSumcheckProver` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckProver` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:853](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L853) — The prover for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:474](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L474) — The prover for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:773](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L773) — The prover for the final sumcheck step

### `finalSumcheckRbrExtractor` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:980](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L980) — The round-by-round extractor for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:621](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L621) — The round-by-round extractor for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1034](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1034) — The round-by-round extractor for the final sumcheck step

### `finalSumcheckVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:895](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L895) — The verifier for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:518](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L518) — The verifier for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:809](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L809) — The verifier for the final sumcheck step

### `fullOracleProof` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:95](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L95) — The full Binary Basefold protocol as a Proof
- `def Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:165](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L165) — The full Binary Basefold protocol as a Proof
- `def RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:80](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L80) — The full Binary Basefold protocol as a Proof

### `fullOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:67](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L67) — The reduction for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:136](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L136) — The reduction for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:68](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L68) — The reduction for the full Binary Basefold protocol

### `fullOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:110](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L110) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:180](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L180) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem RingSwitching.FullRingSwitching.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/General.lean:122](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L122) — (no docstring)

### `fullOracleVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:44](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L44) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:113](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L113) — The oracle verifier for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:51](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L51) — The oracle verifier for the full Binary Basefold protocol

### `knowledgeStateFunction` (3 declarations, 3 files)

- `def CheckClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/CheckClaim.lean:127](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L127) — The knowledge state function for the `CheckClaim` reduction. Since there is no challenge round, the 
- `def RandomQuery.knowledgeStateFunction` [ArkLib/ProofSystem/Component/RandomQuery.lean:230](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L230) — The knowledge state function for the `RandomQuery` oracle reduction.
- `def ReduceClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:134](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L134) — The knowledge state function for the `ReduceClaim` reduction.

### `oracleReduction_completeness` (3 declarations, 3 files)

- `theorem RandomQuery.oracleReduction_completeness` [ArkLib/ProofSystem/Component/RandomQuery.lean:114](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L114) — The `RandomQuery` oracle reduction is perfectly complete.
- `theorem ReduceClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:239](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L239) — The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation.
- `theorem SendSingleWitness.oracleReduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:295](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L295) — The `SendSingleWitness` oracle reduction satisfies perfect completeness.

### `relOut` (3 declarations, 3 files)

- `def CheckClaim.relOut` [ArkLib/ProofSystem/Component/CheckClaim.lean:63](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L63) — (no docstring)
- `def RandomQuery.relOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:49](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L49) — The output relation states that if the verifier's single query was `q`, then `a` and `b` agree on th
- `def SendClaim.relOut` [ArkLib/ProofSystem/Component/SendClaim.lean:98](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L98) — (no docstring)

### `squeeze` (3 declarations, 3 files)

- `def DomainSeparator.squeeze` [ArkLib/Data/Hash/DomainSep.lean:207](../../../ArkLib/Data/Hash/DomainSep.lean#L207) — Squeeze `count` native elements. Rust interface: ```rust pub fn squeeze(self, count: usize, label: &
- `def DuplexSponge.squeeze` [ArkLib/Data/Hash/DuplexSponge.lean:512](../../../ArkLib/Data/Hash/DuplexSponge.lean#L512) — ### Squeeze out a vector of units from the sponge (paper version) We differ from the paper version i
- `def HashStateWithInstructions.squeeze` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:139](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L139) — Perform a secure squeeze operation. Rust interface: ```rust pub fn squeeze(&mut self, output: &mut [

### `cast_id` (9 declarations, 2 files)

- `theorem Prover.cast_id` [ArkLib/OracleReduction/Cast.lean:53](../../../ArkLib/OracleReduction/Cast.lean#L53) — (no docstring)
- `theorem OracleProver.cast_id` [ArkLib/OracleReduction/Cast.lean:77](../../../ArkLib/OracleReduction/Cast.lean#L77) — (no docstring)
- `theorem Verifier.cast_id` [ArkLib/OracleReduction/Cast.lean:99](../../../ArkLib/OracleReduction/Cast.lean#L99) — (no docstring)
- `theorem Reduction.cast_id` [ArkLib/OracleReduction/Cast.lean:284](../../../ArkLib/OracleReduction/Cast.lean#L284) — (no docstring)
- `theorem ProtocolSpec.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:36](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L36) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:80](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L80) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:124](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L124) — (no docstring)
- `theorem ProtocolSpec.Transcript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:168](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L168) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:198](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L198) — (no docstring)

### `seqCompose` (8 declarations, 2 files)

- `def Prover.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:37](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L37) — Sequential composition of provers, defined via iteration of the composition (append) of two provers.
- `def Verifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:75](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L75) — Sequential composition of verifiers, defined via iteration of the composition (append) of two verifi
- `def Reduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:104](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L104) — Sequential composition of reductions, defined via sequential composition of provers and verifiers (o
- `def OracleProver.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:135](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L135) — Sequential composition of provers in oracle reductions, defined via sequential composition of prover
- `def OracleVerifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:182](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L182) — Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the comp
- `def OracleReduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:250](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L250) — Sequential composition of oracle reductions, defined via sequential composition of oracle provers an
- `def ProtocolSpec.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:286](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L286) — Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`. Defined for definitio
- `def ProtocolSpec.FullTranscript.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:344](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L344) — Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`. Defined for definit

### `seqCompose_zero` (7 declarations, 2 files)

- `lemma Prover.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:48](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L48) — (no docstring)
- `lemma Verifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:83](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L83) — (no docstring)
- `lemma Reduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:113](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L113) — (no docstring)
- `lemma OracleVerifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:196](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L196) — (no docstring)
- `lemma OracleReduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:266](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L266) — (no docstring)
- `theorem ProtocolSpec.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:302](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L302) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:349](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L349) — (no docstring)

### `completeness` (5 declarations, 2 files)

- `def Reduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:83](../../../ArkLib/OracleReduction/Security/Basic.lean#L83) — A reduction satisfies **completeness** with regards to: - an initialization function `init : ProbCom
- `def OracleReduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:365](../../../ArkLib/OracleReduction/Security/Basic.lean#L365) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:419](../../../ArkLib/OracleReduction/Security/Basic.lean#L419) — (no docstring)
- `def OracleProof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:448](../../../ArkLib/OracleReduction/Security/Basic.lean#L448) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `theorem SendClaim.completeness` [ArkLib/ProofSystem/Component/SendClaim.lean:110](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L110) — (no docstring)

### `concat` (5 declarations, 2 files)

- `def ProtocolSpec.MessagesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:404](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L404) — Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming round `
- `def ProtocolSpec.ChallengesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:463](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L463) — Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming rou
- `abbrev ProtocolSpec.Transcript.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:516](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L516) — Concatenate a message to the end of a partial transcript. This is definitionally equivalent to `Fin.
- `abbrev ProtocolSpec.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:31](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L31) — Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec`
- `def ProtocolSpec.FullTranscript.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:155](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L155) — Adding a message with a given direction and type to the end of a `Transcript`

### `knowledgeSoundness` (5 declarations, 2 files)

- `def Verifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:272](../../../ArkLib/OracleReduction/Security/Basic.lean#L272) — A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and wit
- `def OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:394](../../../ArkLib/OracleReduction/Security/Basic.lean#L394) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:435](../../../ArkLib/OracleReduction/Security/Basic.lean#L435) — (no docstring)
- `def OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:473](../../../ArkLib/OracleReduction/Security/Basic.lean#L473) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.knowledgeSoundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:141](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L141) — State-restoration knowledge soundness (w/ straightline extractor).

### `new` (5 declarations, 2 files)

- `def DomainSeparator.Op.new` [ArkLib/Data/Hash/DomainSep.lean:138](../../../ArkLib/Data/Hash/DomainSep.lean#L138) — Construct a new `Op` from a character `id` and a count number `count : Option Nat`. Returns error if
- `def DomainSeparator.new` [ArkLib/Data/Hash/DomainSep.lean:159](../../../ArkLib/Data/Hash/DomainSep.lean#L159) — Create a new DomainSeparator with the domain separator. Rust interface: ```rust pub fn new(session_i
- `def HashStateWithInstructions.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:97](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L97) — Initialize a stateful hash object from a domain separator. Rust interface: ```rust pub fn new(domain
- `def FSVerifierState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:238](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L238) — Create a new VerifierState from a domain separator and NARG string. Rust interface: ```rust pub fn n
- `def FSProverState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:379](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L379) — Create a new `FSProverState` from a domain separator and RNG. Rust interface: ```rust pub fn new(dom

### `soundness` (5 declarations, 2 files)

- `def Verifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:239](../../../ArkLib/OracleReduction/Security/Basic.lean#L239) — A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input langua
- `def OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:386](../../../ArkLib/OracleReduction/Security/Basic.lean#L386) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:429](../../../ArkLib/OracleReduction/Security/Basic.lean#L429) — (no docstring)
- `def OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:465](../../../ArkLib/OracleReduction/Security/Basic.lean#L465) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.soundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:127](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L127) — State-restoration soundness

### `cast_eq_dcast₂` (4 declarations, 2 files)

- `theorem Verifier.cast_eq_dcast₂` [ArkLib/OracleReduction/Cast.lean:107](../../../ArkLib/OracleReduction/Cast.lean#L107) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:92](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L92) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:136](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L136) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:204](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L204) — (no docstring)

### `instDCast₂` (4 declarations, 2 files)

- `instance Prover.instDCast₂` [ArkLib/OracleReduction/Cast.lean:60](../../../ArkLib/OracleReduction/Cast.lean#L60) — (no docstring)
- `instance ProtocolSpec.MessageIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:88](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L88) — (no docstring)
- `instance ProtocolSpec.ChallengeIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:132](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L132) — (no docstring)
- `instance ProtocolSpec.FullTranscript.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:200](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L200) — (no docstring)

### `subdomain` (4 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:75](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L75) — Given a smooth coset FFT domain `ω` of log-order `n` this function returns its subdomain of log-orde
- `abbrev Domain.CosetFftDomain.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:408](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L408) — (no docstring)
- `def Domain.FftDomainClass.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:32](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L32) — (no docstring)
- `abbrev Domain.FftDomain.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:122](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L122) — (no docstring)

### `accepts` (3 declarations, 2 files)

- `def Plonk.Gate.accepts` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:58](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L58) — A gate accepts an input vector `x` if its evaluation at `x` is zero.
- `def Plonk.ConstraintSystem.accepts` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:129](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L129) — A constraint system accepts an input vector `x` if all of its gates accept `x`.
- `def ToyProblem.Spec.accepts` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:165](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L165) — The §6.1 decision predicate, factored out so completeness proofs and the verifier object share the s

### `advantage` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.advantage` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:409](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L409) — Weak-binding advantage.
- `def ArkLib.Lattices.SIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:62](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L62) — Search advantage for a SIS-style problem.
- `def ArkLib.Lattices.ModuleSIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:108](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L108) — The Module-SIS advantage.

### `correctness` (3 declarations, 2 files)

- `def Commitment.correctness` [ArkLib/CommitmentScheme/Basic.lean:88](../../../ArkLib/CommitmentScheme/Basic.lean#L88) — A commitment scheme satisfies **correctness** with error `correctnessError` if for all `data : Data`
- `theorem KZG.correctness` [ArkLib/CommitmentScheme/KZG/Correctness.lean:51](../../../ArkLib/CommitmentScheme/KZG/Correctness.lean#L51) — Algebraic correctness of one KZG opening for a coefficient vector.
- `theorem KZG.CommitmentScheme.correctness` [ArkLib/CommitmentScheme/KZG/Correctness.lean:161](../../../ArkLib/CommitmentScheme/KZG/Correctness.lean#L161) — The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

### `experiment` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.experiment` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:396](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L396) — The Hachi/Greyhound weak-binding experiment. ## Ordinary vs. weak binding *Ordinary (exact) binding*
- `def ArkLib.Lattices.SIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:56](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L56) — The SIS experiment: sample a challenge, run the adversary, check validity.
- `def ArkLib.Lattices.ModuleSIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:102](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L102) — The Module-SIS experiment.

### `extract` (3 declarations, 2 files)

- `def Fin.extract` [ArkLib/Data/Fin/Tuple/Defs.lean:73](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L73) — Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`.
- `def ProtocolSpec.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:125](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L125) — Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`.
- `abbrev ProtocolSpec.FullTranscript.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:182](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L182) — (no docstring)

### `mem_toFinset_iff_mem` (3 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:61](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L61) — (no docstring)
- `lemma Domain.CosetFftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:102](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L102) — (no docstring)
- `lemma Domain.FftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/FftDomain/Mem.lean:60](../../../ArkLib/Data/Domain/FftDomain/Mem.lean#L60) — (no docstring)

### `rdrop` (3 declarations, 2 files)

- `abbrev Fin.rdrop` [ArkLib/Data/Fin/Tuple/Defs.lean:68](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L68) — Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. This is defi
- `def ProtocolSpec.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:121](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L121) — Drop the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:178](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L178) — (no docstring)

### `rtake` (3 declarations, 2 files)

- `def Fin.rtake` [ArkLib/Data/Fin/Tuple/Defs.lean:55](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L55) — Take the last `m` elements of a finite vector
- `def ProtocolSpec.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:113](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L113) — Take the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:170](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L170) — Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec`

### `ChallengeIdx` (2 declarations, 2 files)

- `def ProtocolSpec.ChallengeIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:54](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L54) — Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification
- `def ProtocolSpec.VectorSpec.ChallengeIdx` [ArkLib/OracleReduction/VectorIOR.lean:54](../../../ArkLib/OracleReduction/VectorIOR.lean#L54) — The type of indices for challenges in a `VectorSpec`.

### `Commitment` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Commitment` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:126](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L126) — Inner-outer commitments live in the outer row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Commitment` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:35](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L35) — Commitments: row vectors over `Rq Φ`.

### `ConstraintSystem` (2 declarations, 2 files)

- `structure ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:49](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L49) — A **constraint system** packages a family of indexed relations into a single bundle. For each `i : I
- `def Plonk.ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:116](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L116) — A Plonk constraint system is a vector of `numGates` gates, each parametrized by the underlying ring 

### `FinalSumcheckWit` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:974](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L974) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:615](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L615) — (no docstring)

### `GenMutualCorrParams` (2 declarations, 2 files)

- `class Fold.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/Folding.lean:165](../../../ArkLib/ProofSystem/Whir/Folding.lean#L165) — The `GenMutualCorrParams` class captures the necessary parameters and assumptions to model a sequenc
- `class WhirIOP.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:85](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L85) — `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes `C_{i : M + 1, j : foldingPar

### `MessageIdx` (2 declarations, 2 files)

- `def ProtocolSpec.MessageIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:49](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L49) — Subtype of `Fin n` for the indices corresponding to messages in a protocol specification
- `def ProtocolSpec.VectorSpec.MessageIdx` [ArkLib/OracleReduction/VectorIOR.lean:50](../../../ArkLib/OracleReduction/VectorIOR.lean#L50) — The type of indices for messages in a `VectorSpec`.

### `OutputOracleStatement` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:105](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L105) — Output oracle statement: the IOR has no output oracle component.
- `def ToyProblem.SimplifiedIOR.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:76](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L76) — Output oracle statement: the single combined codeword `f_new := f₁ + γ·f₂ : ι → F`.

### `OutputWitness` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:109](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L109) — Output witness: empty.
- `def ToyProblem.SimplifiedIOR.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:80](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L80) — Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`.

### `ParamConditions` (2 declarations, 2 files)

- `structure StirIOP.ParamConditions` [ArkLib/ProofSystem/Stir/MainThm.lean:52](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L52) — **Conditions that protocol parameters must satisfy.** - `h_deg` : initial degree `deg` is a power of
- `structure WhirIOP.ParamConditions` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:66](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L66) — ** Conditions that protocol parameters must satisfy. ** h_m : m = varCount₀ h_sumkLt : ∑ i : Fin (M 

### `SumcheckMultiplierParam` (2 declarations, 2 files)

- `structure Sumcheck.Structured.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured.lean:85](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L85) — Parameters describing how the round polynomial `H` is built from the witness `t`: `H = P · Q(t)`, wh
- `structure Sumcheck.Structured.Prismalinear.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:50](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L50) — Parameters describing how a *prismalinear* round polynomial `H = P · Q(t)` is built from the witness

### `SumcheckWitness` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckWitness` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:234](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L234) — (no docstring)
- `structure Sumcheck.Structured.SumcheckWitness` [ArkLib/ProofSystem/Sumcheck/Structured.lean:231](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L231) — Witness for the structured sumcheck at round `i`: - `t'` — the original multilinear polynomial (the 

### `WitIn` (2 declarations, 2 files)

- `def RandomQuery.WitIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:36](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L36) — (no docstring)
- `def Logup.WitIn` [ArkLib/ProofSystem/Logup/Common.lean:249](../../../ArkLib/ProofSystem/Logup/Common.lean#L249) — Protocol 2 has no private witness beyond the input oracles at this layer.

### `answer_instDefault` (2 declarations, 2 files)

- `lemma RingSwitching.BatchingPhase.answer_instDefault` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:54](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L54) — The default oracle interface (`OracleInterface.instDefault`, used by the ring-switching message orac
- `lemma ToyProblem.Spec.answer_instDefault` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:479](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L479) — `answer` of the default oracle interface is the identity (the message itself).

### `append_left_injective` (2 declarations, 2 files)

- `theorem Fin.append_left_injective` [ArkLib/Data/Fin/Basic.lean:262](../../../ArkLib/Data/Fin/Basic.lean#L262) — (no docstring)
- `theorem ProtocolSpec.append_left_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:55](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L55) — (no docstring)

### `append_right_injective` (2 declarations, 2 files)

- `theorem Fin.append_right_injective` [ArkLib/Data/Fin/Basic.lean:270](../../../ArkLib/Data/Fin/Basic.lean#L270) — (no docstring)
- `theorem ProtocolSpec.append_right_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:65](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L65) — (no docstring)

### `batchingCoreReduction` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:96](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L96) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:58](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L58) — (no docstring)

### `batchingCoreVerifier` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:82](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L82) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:42](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L42) — (no docstring)

### `binding` (2 declarations, 2 files)

- `def Commitment.binding` [ArkLib/CommitmentScheme/Basic.lean:170](../../../ArkLib/CommitmentScheme/Basic.lean#L170) — A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all adversar
- `theorem KZG.CommitmentScheme.binding` [ArkLib/CommitmentScheme/KZG/Binding.lean:737](../../../ArkLib/CommitmentScheme/KZG/Binding.lean#L737) — The KZG scheme satisfies evaluation binding provided `t`-SDH holds.

### `biniusProfile` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:56](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L56) — The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def
- `def Binius.FRIBinius.FullFRIBinius.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:51](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L51) — The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def

### `coeffHom` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:175](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L175) — Reading off the `k`-th coefficient of the underlying polynomial, as an additive homomorphism `Rq Φ →
- `def CompPoly.CPolynomial.coeffHom` [ArkLib/ToCompPoly/Univariate/Basic.lean:284](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L284) — Extracting the `k`-th coefficient as an additive homomorphism.

### `coeffHom_apply` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom_apply` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:180](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L180) — (no docstring)
- `theorem CompPoly.CPolynomial.coeffHom_apply` [ArkLib/ToCompPoly/Univariate/Basic.lean:290](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L290) — (no docstring)

### `computeRoundPoly` (2 declarations, 2 files)

- `def Sumcheck.Structured.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured.lean:130](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L130) — The general round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` is the public multilinea
- `def Sumcheck.Structured.Prismalinear.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:69](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L69) — The *prismalinear* round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` has per-variable 

### `coreInteractionOracleRbrKnowledgeError` (2 declarations, 2 files)

- `def coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:647](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L647) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:810](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L810) — (no docstring)

### `coreInteractionOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:629](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L629) — Perfect completeness for the core interaction oracle reduction
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:786](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L786) — Perfect completeness for the core interaction oracle reduction

### `coreInteractionOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:655](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L655) — Round-by-round knowledge soundness for the core interaction oracle verifier
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:819](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L819) — Round-by-round knowledge soundness for the core interaction oracle verifier

### `decoder` (2 declarations, 2 files)

- `def BerlekampWelch.decoder` [ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:52](../../../ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean#L52) — Berlekamp-Welch decoder for Reed-Solomon codes. Given received codeword evaluations with potential e
- `opaque GuruswamiSudan.decoder` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:75](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L75) — Specification-level Guruswami-Sudan decoder.

### `domain_implies_char_ne_2` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:88](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L88) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:125](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L125) — (no docstring)

### `extractor` (2 declarations, 2 files)

- `def CheckClaim.extractor` [ArkLib/ProofSystem/Component/CheckClaim.lean:120](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L120) — The round-by-round extractor for the `CheckClaim` reduction. Trivial since the witness is `Unit`.
- `def ReduceClaim.extractor` [ArkLib/ProofSystem/Component/ReduceClaim.lean:112](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L112) — The round-by-round extractor for the `ReduceClaim` (oracle) reduction. Requires a mapping `mapWitInv

### `finalSumcheckKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:969](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L969) — RBR knowledge error for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:610](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L610) — RBR knowledge error for the final sumcheck step

### `foldOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.foldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:198](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L198) — The oracle reduction that is the `i`-th round of Binary Foldfold.
- `def Fri.Spec.FoldPhase.foldOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:463](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L463) — The oracle reduction that is the `i`-th round of the FRI protocol.

### `fullOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:150](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L150) — Round-by-round knowledge soundness for the full Binary Basefold oracle verifier
- `theorem RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/General.lean:152](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L152) — Round-by-round knowledge soundness for the full ring-switching oracle verifier. `IsDomain K` (with t

### `fullPspec` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.fullPspec` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:59](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L59) — (no docstring)
- `def RingSwitching.fullPspec` [ArkLib/ProofSystem/RingSwitching/Spec.lean:56](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L56) — (no docstring)

### `fullRbrKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:140](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L140) — Combined RBR knowledge soundness error for the full protocol
- `def RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/General.lean:140](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L140) — (no docstring)

### `getSumcheckRoundPoly_eval_eq_sum_snoc` (2 declarations, 2 files)

- `theorem RingSwitching.SumcheckPhase.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:284](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L284) — **Target (b): `getSumcheckRoundPoly` value as a cube sum (LAST-variable/`snoc` form, defect-#20 repa
- `theorem Sumcheck.Structured.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:116](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L116) — **Round-univariate evaluation as a survivor-cube sum (last-variable / `snoc` form).** Evaluating the

### `guruswami_sudan_for_proximity_gap_existence` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:741](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L741) — Constructive witness extraction for the Guruswami–Sudan system. When the computable `hasWitnessC` ch
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:189](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L189) — The first part of Lemma 5.3 from [BCIKS20]. Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`pr

### `guruswami_sudan_for_proximity_gap_property` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:780](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L780) — Constructive witness property for the Guruswami–Sudan system. When `m > 0` and the codeword polynomi
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:201](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L201) — The second part of Lemma 5.3 from [BCIKS20]. For any solution `Q` of the Guruswami-Sudan system, and

### `hint` (2 declarations, 2 files)

- `def DomainSeparator.hint` [ArkLib/Data/Hash/DomainSep.lean:196](../../../ArkLib/Data/Hash/DomainSep.lean#L196) — Hint `count` native elements. Rust interface: ```rust pub fn hint(self, label: &str) -> Self ```
- `def HashStateWithInstructions.hint` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:171](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L171) — Process a hint operation. Rust interface: ```rust pub fn hint(&mut self) -> Result<(), DomainSeparat

### `injOn` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injOn` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:220](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L220) — (no docstring)
- `lemma Domain.FftDomain.injOn` [ArkLib/Data/Domain/FftDomain/Defs.lean:104](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L104) — (no docstring)

### `injective` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injective` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:215](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L215) — (no docstring)
- `lemma Domain.FftDomain.injective` [ArkLib/Data/Domain/FftDomain/Defs.lean:100](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L100) — (no docstring)

### `leftpad` (2 declarations, 2 files)

- `def Fin.leftpad` [ArkLib/Data/Fin/Tuple/Defs.lean:96](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L96) — Pad a `Fin`-indexed vector on the left with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.leftpad` [ArkLib/Data/Matrix/Basic.lean:25](../../../ArkLib/Data/Matrix/Basic.lean#L25) — (no docstring)

### `liftContext_completeness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:118](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L118) — (no docstring)
- `theorem Reduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:419](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L419) — Lifting the reduction preserves completeness, assuming the lens satisfies its completeness condition

### `liftContext_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:155](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L155) — (no docstring)
- `theorem Verifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:663](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L663) — (no docstring)

### `liftContext_perfectCompleteness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:125](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L125) — (no docstring)
- `theorem Reduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:459](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L459) — (no docstring)

### `liftContext_rbr_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:186](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L186) — (no docstring)
- `theorem Verifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1084](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1084) — (no docstring)

### `liftContext_rbr_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:172](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L172) — (no docstring)
- `theorem Verifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:993](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L993) — (no docstring)

### `liftContext_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:142](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L142) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
- `theorem Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:514](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L514) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions

### `masterKStateProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.masterKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1041](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1041) — Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event of the `i-th` oracle if
- `def RingSwitching.masterKStateProp` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:442](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L442) — (no docstring)

### `ofFinCoeff` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.Rq.ofFinCoeff` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:184](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L184) — The reduced representative with prescribed finite coefficients `Σ_{k<N} cₖ Xᵏ`, valid when `N` does 
- `def CompPoly.CPolynomial.ofFinCoeff` [ArkLib/ToCompPoly/Univariate/Basic.lean:293](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L293) — The polynomial with prescribed finite coefficient function: `Σ_{k<N} cₖ Xᵏ`.

### `oracleVerifier_toVerifier_run` (2 declarations, 2 files)

- `theorem ReduceClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/ReduceClaim.lean:205](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L205) — Running the (oracle) verifier of the `ReduceClaim` oracle reduction deterministically returns the ma
- `theorem SendSingleWitness.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendWitness.lean:268](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L268) — (no docstring)

### `pSpecCoreInteraction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:248](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L248) — (no docstring)
- `def RingSwitching.pSpecCoreInteraction` [ArkLib/ProofSystem/RingSwitching/Spec.lean:49](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L49) — (no docstring)

### `pSpecFold` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecFold` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:201](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L201) — (no docstring)
- `def Fri.Spec.pSpecFold` [ArkLib/ProofSystem/Fri/Spec/General.lean:57](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L57) — (no docstring)

### `pSpecSumcheckRound` (2 declarations, 2 files)

- `abbrev RingSwitching.pSpecSumcheckRound` [ArkLib/ProofSystem/RingSwitching/Spec.lean:41](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L41) — (no docstring)
- `def Sumcheck.Structured.pSpecSumcheckRound` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:148](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L148) — Protocol spec for one round of the structured sumcheck: P sends a degree-≤`d` univariate `h_i(X) ∈ L

### `perfectlyCorrect` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Ajtai.InnerOuter.perfectlyCorrect` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Correctness.lean:198](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Correctness.lean#L198) — **Unconditional perfect correctness with the concrete binary decomposition.** Both message and inner
- `theorem ArkLib.Lattices.Ajtai.Simple.perfectlyCorrect` [ArkLib/CommitmentScheme/Ajtai/Simple/Correctness.lean:33](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Correctness.lean#L33) — Simple Ajtai commitments are correct on short messages: an honest commitment to a message accepted b

### `proximityCondition` (2 declarations, 2 files)

- `def MutualCorrAgreement.proximityCondition` [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:56](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean#L56) — For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽` and linea
- `def Generator.proximityCondition` [ArkLib/ProofSystem/Whir/ProximityGen.lean:42](../../../ArkLib/ProofSystem/Whir/ProximityGen.lean#L42) — For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽ˡ` and linear 

### `queryCodeword` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryCodeword` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:439](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L439) — Oracle query helper: query a committed codeword at a given domain point. Restricted to codeword indi
- `def Fri.Spec.QueryRound.queryCodeword` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:820](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L820) — (no docstring)

### `queryOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:631](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L631) — The oracle reduction for the final query phase.
- `def Fri.Spec.QueryRound.queryOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:938](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L938) — (no docstring)

### `reduction_verifier_eq_verifier` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:193](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L193) — (no docstring)
- `lemma Sumcheck.Spec.SingleRound.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1133](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1133) — (no docstring)

### `relIn` (2 declarations, 2 files)

- `def CheckClaim.relIn` [ArkLib/ProofSystem/Component/CheckClaim.lean:60](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L60) — (no docstring)
- `def RandomQuery.relIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:41](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L41) — The input relation is that the two oracles are equal.

### `rightpad` (2 declarations, 2 files)

- `def Fin.rightpad` [ArkLib/Data/Fin/Tuple/Defs.lean:90](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L90) — Pad a `Fin`-indexed vector on the right with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.rightpad` [ArkLib/Data/Matrix/Basic.lean:21](../../../ArkLib/Data/Matrix/Basic.lean#L21) — (no docstring)

### `roundKnowledgeError` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckPhase.roundKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:264](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L264) — (no docstring)
- `def Sumcheck.Structured.roundKnowledgeError` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:343](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L343) — Round-by-round knowledge error for a single round of the structured sumcheck: the Schwartz–Zippel bo

### `run` (2 declarations, 2 files)

- `def AGM.Adversary.run` [ArkLib/AGM/Basic.lean:165](../../../ArkLib/AGM/Basic.lean#L165) — Running the adversary on a given table, returning the list of group elements it is supposed to outpu
- `def Prover.run` [ArkLib/OracleReduction/Execution.lean:140](../../../ArkLib/OracleReduction/Execution.lean#L140) — Run the prover in an interactive reduction. Returns the output statement and witness, and the transc

### `simulateQ_optionT_forIn` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.QueryPhase.ForInSupport.simulateQ_optionT_forIn` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:236](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L236) — `simulateQ` commutes with `forIn` over a list in the `OptionT (OracleComp …)` monad: simulating a lo
- `theorem ToyProblem.Spec.simulateQ_optionT_forIn` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:512](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L512) — `simulateQ` commutes with `forIn` over a list in `OptionT (OracleComp …)`: the simulated loop equals

### `simulateQ_optionT_pure` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.QueryPhase.ForInSupport.simulateQ_optionT_pure` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:225](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L225) — `simulateQ` commutes with `OptionT.pure`.
- `theorem ToyProblem.Spec.simulateQ_optionT_pure` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:487](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L487) — `simulateQ` commutes with `OptionT.pure`.

### `simulateQ_oracleVerify_eq` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.SingleRound.Simple.simulateQ_oracleVerify_eq` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:830](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L830) — Closed form of the simulated oracle-verifier `verify`: the inner `simOracle2` simulation collapses t
- `theorem ToyProblem.Spec.simulateQ_oracleVerify_eq` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:639](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L639) — **Closed form of the compiled toy-problem oracle verifier.** Simulating `oracleVerifier.verify` agai

### `simulateQ_simOracle2_leftQuery_oc` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.QueryPhase.ForInSupport.simulateQ_simOracle2_leftQuery_oc` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:302](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L302) — **`simOracle2` oracle-statement-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oS
- `lemma ToyProblem.Spec.simulateQ_simOracle2_leftQuery_oc` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:584](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L584) — `simOracle2` oracle-statement-query collapse (`OracleComp` form), LEFT (oracle) family.

### `simulateQ_simOracle2_messageQuery` (2 declarations, 2 files)

- `lemma RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1412](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1412) — **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
- `lemma ToyProblem.Spec.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:569](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L569) — `simOracle2` message-query collapse (`OracleComp` form), RIGHT (message) family.

### `sumcheckFoldOracleReduction` (2 declarations, 2 files)

- `def sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:503](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L503) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:145](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L145) — (no docstring)

### `sumcheckFoldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:551](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L551) — Perfect completeness for the core interaction oracle reduction
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:233](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L233) — (no docstring)

### `sumcheckFoldOracleVerifier` (2 declarations, 2 files)

- `def sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:340](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L340) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:139](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L139) — (no docstring)

### `sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:575](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L575) — Round-by-round knowledge soundness for the sumcheck fold oracle verifier
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:389](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L389) — (no docstring)

### `vecL2NormSq` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:91](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L91) — Centered squared-`ℓ₂` norm of a vector: the sum of entrywise norms.
- `def ArkLib.Lattices.CenteredCoeffView.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/Norms.lean:80](../../../ArkLib/Data/Lattices/CyclotomicRing/Norms.lean#L80) — Vector squared `ℓ₂` norm: the sum of entrywise squared `ℓ₂` norms.

### `verify` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.Simple.verify` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:46](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L46) — Verify a simple Ajtai opening by checking the matrix product.
- `def SimpleRO.verify` [ArkLib/CommitmentScheme/SimpleRO.lean:50](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L50) — (no docstring)

### `witnessStructuralInvariant` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:818](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L818) — This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
- `def RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:435](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L435) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`

### `OracleInterface` (3 declarations, 2 files)

- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:88](../../../ArkLib/OracleReduction/Basic.lean#L88) — (no docstring)
- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:162](../../../ArkLib/OracleReduction/Basic.lean#L162) — (no docstring)
- `class OracleInterface` [ArkLib/OracleReduction/OracleInterface.lean:52](../../../ArkLib/OracleReduction/OracleInterface.lean#L52) — `OracleInterface` is a type class that provides an oracle interface for a type `Message`. It consist

### `card_agreement_le` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.card_agreement_le` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:100](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L100) — The agreement set of two distinct codewords' polynomials (inside any subtype of `F`) has at most `de
- `lemma OutOfDomSmpl.card_agreement_le` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:197](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L197) — Two distinct smooth codewords' decoded polynomials agree on at most `2^m - 1` field points: agreemen

### `card_filter_forall_pi` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.card_filter_forall_pi` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:69](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L69) — Counting a coordinatewise event: the tuples satisfying `Q` in every coordinate form the `piFinset` o
- `lemma OutOfDomSmpl.card_filter_forall_pi` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:169](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L169) — Tuples satisfying `Q` in every coordinate form the `piFinset` of the per-coordinate solution set, so

### `decodeLT_ne_of_val_ne` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:85](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L85) — Distinct codewords decode to distinct polynomials: the decoded polynomial interpolates the codeword 
- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:183](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L183) — Distinct smooth codewords decode to distinct univariate polynomials (the decoded polynomial interpol

### `uniform_event_mass` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:53](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L53) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly
- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:154](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L154) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly

## Near-duplicate docstrings (Jaccard ≥ 0.85, 63 cross-file pairs)

Each pair has docstrings sharing a high fraction of (4+-letter) words, in different files. Most are unrelated coincidences in boilerplate; look for pairs where the *concept* matches.

- **1.00** `Binius.BinaryBasefold.CoreInteraction.commitKState` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:589](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L589) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:527](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L527)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.commitOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:610](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L610) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:734](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L734)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:969](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L969) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:610](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L610)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:969](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L969) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1031](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1031)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1044](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1044) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:695](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L695)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1044](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1044) vs `RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1091](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1091)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:939](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L939) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:571](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L571)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:939](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L939) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:867](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L867)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:953](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L953) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:587](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L587)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:953](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L953) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:960](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L960)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1064](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1064) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:724](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L724)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1064](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1064) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1212](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1212)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:980](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L980) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:621](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L621)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:980](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L980) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1034](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1034)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.foldKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:343](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L343) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:527](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L527)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.foldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:374](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L374) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:734](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L734)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.CoreInteraction.relayKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:750](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L750) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:527](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L527)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.relayOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:807](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L807) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:734](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L734)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:95](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L95) vs `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:165](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L165)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:95](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L95) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:80](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L80)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:67](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L67) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:136](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L136)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:67](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L67) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:68](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L68)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:110](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L110) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:180](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L180)
    - a: Perfect completeness for the full Binary Basefold protocol (reduction)
    - b: Perfect completeness for the full Binary Basefold protocol (reduction)
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:44](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L44) vs `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:113](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L113)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:44](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L44) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:51](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L51)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.QueryPhase.ForInSupport.simulateQ_optionT_pure` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:225](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L225) vs `ToyProblem.Spec.simulateQ_optionT_pure` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:487](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L487)
    - a: `simulateQ` commutes with `OptionT.pure`.
    - b: `simulateQ` commutes with `OptionT.pure`.
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:818](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L818) vs `RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:435](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L435)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:56](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L56) vs `Binius.FRIBinius.FullFRIBinius.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:51](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L51)
    - a: The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def
    - b: The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:610](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L610) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1031](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1031)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:695](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L695) vs `RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1091](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1091)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:571](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L571) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:867](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L867)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:587](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L587) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:960](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L960)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:724](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L724) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1212](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1212)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:621](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L621) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1034](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1034)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:165](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L165) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:80](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L80)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:136](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L136) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:68](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L68)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:113](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L113) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:51](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L51)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Groups.exists_zmod_power_of_generator` [ArkLib/CommitmentScheme/KZG/Algebra.lean:105](../../../ArkLib/CommitmentScheme/KZG/Algebra.lean#L105) vs `KZG.CommitmentScheme.binding_exists_zmod_power_of_generator` [ArkLib/CommitmentScheme/KZG/Binding.lean:167](../../../ArkLib/CommitmentScheme/KZG/Binding.lean#L167)
    - a: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
    - b: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
- **1.00** `Groups.orderOf_eq_prime_of_ne_one` [ArkLib/CommitmentScheme/KZG/Algebra.lean:61](../../../ArkLib/CommitmentScheme/KZG/Algebra.lean#L61) vs `KZG.CommitmentScheme.binding_order_of_eq_prime_of_ne_one` [ArkLib/CommitmentScheme/KZG/Binding.lean:157](../../../ArkLib/CommitmentScheme/KZG/Binding.lean#L157)
    - a: A nontrivial element of a prime-order group has order `p`.
    - b: A nontrivial element of a prime-order group has order `p`.
- **1.00** `KZG.CommitmentScheme.map_binding_instance_drag` [ArkLib/CommitmentScheme/KZG/Binding.lean:639](../../../ArkLib/CommitmentScheme/KZG/Binding.lean#L639) vs `KZG.CommitmentScheme.map_instance_drag` [ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean:534](../../../ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean#L534)
    - a: Transition 3: dragging the map into the probability event.
    - b: Transition 3: dragging the map into the probability event
- **1.00** `OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:142](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L142) vs `Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:514](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L514)
    - a: Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
    - b: Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
- **1.00** `Prover.processRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:78](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L78) vs `Prover.processRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:167](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L167)
    - a: Prover's function for processing the next round, given the current result of the previous round. Thi
    - b: Prover's function for processing the next round, given the current result of the previous round. Thi
- **1.00** `Prover.runToRound` [ArkLib/OracleReduction/Execution.lean:103](../../../ArkLib/OracleReduction/Execution.lean#L103) vs `Prover.runToRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:197](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L197)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
- **1.00** `Prover.runToRound` [ArkLib/OracleReduction/Execution.lean:103](../../../ArkLib/OracleReduction/Execution.lean#L103) vs `Prover.runToRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:100](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L100)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
- **1.00** `Prover.runToRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:100](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L100) vs `Prover.runToRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:197](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L197)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
- **1.00** `StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:81](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L81) vs `WhirIOP.OracleStatement` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:146](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L146)
    - a: `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
    - b: `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- **1.00** `StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:32](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L32) vs `WhirIOP.Params` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:54](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L54)
    - a: **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun
    - b: ** Per‑round protocol parameters. ** For a fixed depth `M`, the reduction runs `M + 1` rounds. In ro
- **1.00** `coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:610](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L610) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:764](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L764)
    - a: The final oracle reduction that composes sumcheckFold with finalSumcheckStep
    - b: The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- **1.00** `coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:629](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L629) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:786](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L786)
    - a: Perfect completeness for the core interaction oracle reduction
    - b: Perfect completeness for the core interaction oracle reduction
- **1.00** `coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:595](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L595) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:746](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L746)
    - a: The final oracle verifier that composes sumcheckFold with finalSumcheckStep
    - b: The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- **1.00** `coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:655](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L655) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:819](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L819)
    - a: Round-by-round knowledge soundness for the core interaction oracle verifier
    - b: Round-by-round knowledge soundness for the core interaction oracle verifier
- **1.00** `sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:551](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L551) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:786](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L786)
    - a: Perfect completeness for the core interaction oracle reduction
    - b: Perfect completeness for the core interaction oracle reduction
- **0.88** `OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:473](../../../ArkLib/OracleReduction/Security/Basic.lean#L473) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:504](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L504)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:473](../../../ArkLib/OracleReduction/Security/Basic.lean#L473) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:461](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L461)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:394](../../../ArkLib/OracleReduction/Security/Basic.lean#L394) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:504](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L504)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:394](../../../ArkLib/OracleReduction/Security/Basic.lean#L394) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:461](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L461)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:465](../../../ArkLib/OracleReduction/Security/Basic.lean#L465) vs `OracleProof.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:496](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L496)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:465](../../../ArkLib/OracleReduction/Security/Basic.lean#L465) vs `OracleVerifier.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:452](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L452)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleVerifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:633](../../../ArkLib/OracleReduction/Security/Basic.lean#L633) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:581](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L581)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:386](../../../ArkLib/OracleReduction/Security/Basic.lean#L386) vs `OracleProof.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:496](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L496)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:386](../../../ArkLib/OracleReduction/Security/Basic.lean#L386) vs `OracleVerifier.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:452](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L452)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `Verifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:591](../../../ArkLib/OracleReduction/Security/Basic.lean#L591) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:581](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L581)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `proximity_gap_degree_bound` [ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean:28](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean#L28) vs `ProximityGap.D_X` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:183](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L183)
    - a: The degree bound (i.e. `D_X(m) = (m + 1/2) * √ρ * n`) for instantiation of Guruswami-Sudan in Lemma 
    - b: The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan in Lemma 5.3 of [BCIKS20]. `D_X


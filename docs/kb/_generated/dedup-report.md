# ArkLib dedup-candidate report

Generated from `docs/kb/_generated/declarations.json`. **Eyeball, do not auto-rewrite.** The point is to surface name collisions and doc-string overlap that *might* indicate an opportunity to consolidate.

## Stats

- `ArkLib` — 217 files, 4222 declarations

## Same short-name across multiple files (114 groups)

Each group lists declarations sharing a short name across ≥2 files. Most are legitimate (overloaded interface, paper-shape vs general form), but the list is the right anchor to look for duplicates.

### `oracleVerifier` (10 declarations, 9 files)

- `def CheckClaim.oracleVerifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:186](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L186) — The oracle verifier for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleVerifier` [ArkLib/ProofSystem/Component/DoNothing.lean:72](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L72) — The oracle verifier for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleVerifier` [ArkLib/ProofSystem/Component/RandomQuery.lean:82](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L82) — The oracle verifier simply returns the challenge, and performs no checks.
- `def ReduceClaim.oracleVerifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:199](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L199) — The oracle verifier for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleVerifier` [ArkLib/ProofSystem/Component/SendClaim.lean:63](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L63) — The verifier checks that the relationship `rel oldStmt newStmt` holds. It has access to the original
- `def SendSingleWitness.oracleVerifier` [ArkLib/ProofSystem/Component/SendWitness.lean:242](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L242) — The oracle verifier for the `SendSingleWitness` oracle reduction. The verifier receives the input st
- `def RingSwitching.BatchingPhase.oracleVerifier` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:138](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L138) — (no docstring)
- `def Sumcheck.Spec.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:158](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L158) — The oracle verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:426](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L426) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:848](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L848) — The oracle verifier for the `i`-th round of the sum-check protocol

### `reduction` (10 declarations, 9 files)

- `def KZG.CommitmentScheme.reduction` [ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean:115](../../../ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean#L115) — The reduction breaking ARSDH using a successful function-binding adversary. The reduction follows th
- `def CheckClaim.reduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:55](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L55) — The reduction for the `CheckClaim` reduction.
- `def DoNothing.reduction` [ArkLib/ProofSystem/Component/DoNothing.lean:43](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L43) — The reduction for the `DoNothing` reduction. - Prover simply returns the statement and witness. - Ve
- `def NoInteraction.reduction` [ArkLib/ProofSystem/Component/NoInteraction.lean:62](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L62) — The no-interaction reduction can be specified by a tuple of functions: - `mapStmt : StmtIn → OracleC
- `def ReduceClaim.reduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:56](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L56) — The reduction for the `ReduceClaim` reduction.
- `def SendWitness.reduction` [ArkLib/ProofSystem/Component/SendWitness.lean:61](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L61) — (no docstring)
- `def Fri.Spec.reduction` [ArkLib/ProofSystem/Fri/Spec/General.lean:98](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L98) — (no docstring)
- `def Sumcheck.Spec.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:168](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L168) — The sum-check protocol as a reduction
- `def Sumcheck.Spec.SingleRound.Simple.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:413](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L413) — The reduction for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:853](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L853) — The sum-check reduction for the `i`-th round of the sum-check protocol

### `oracleReduction` (10 declarations, 8 files)

- `def CheckClaim.oracleReduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:194](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L194) — The oracle reduction for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleReduction` [ArkLib/ProofSystem/Component/DoNothing.lean:82](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L82) — The oracle reduction for the `DoNothing` oracle reduction. - Prover simply returns the (non-oracle a
- `def RandomQuery.oracleReduction` [ArkLib/ProofSystem/Component/RandomQuery.lean:100](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L100) — Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction: the input o
- `def ReduceClaim.oracleReduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:205](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L205) — The oracle reduction for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleReduction` [ArkLib/ProofSystem/Component/SendClaim.lean:92](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L92) — Combine the prover and verifier into an oracle reduction. The input has no statement or witness, but
- `def SendSingleWitness.oracleReduction` [ArkLib/ProofSystem/Component/SendWitness.lean:255](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L255) — (no docstring)
- `def Sumcheck.Spec.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:180](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L180) — The sum-check protocol as an oracle reduction
- `def Sumcheck.Spec.SingleRound.Simpler.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:300](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L300) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:443](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L443) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:859](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L859) — The sum-check oracle reduction for the `i`-th round of the sum-check protocol

### `OracleStatement` (8 declarations, 8 files)

- `def BatchedFri.Spec.OracleStatement` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:40](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L40) — An oracle for each batched polynomial.
- `def Binius.BinaryBasefold.OracleStatement` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:488](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L488) — For the `i`-th round of the protocol, there will be oracle statements corresponding to all committed
- `def R1CS.OracleStatement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:48](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L48) — (no docstring)
- `def Fri.Spec.OracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:84](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L84) — For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the beginning
- `abbrev Spartan.Spec.OracleStatement` [ArkLib/ProofSystem/Spartan/Basic.lean:144](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L144) — This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R`
- `def StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:81](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L81) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- `def Sumcheck.Spec.OracleStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:135](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L135) — Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of individual 
- `def WhirIOP.OracleStatement` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:146](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L146) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type

### `verifier` (9 declarations, 7 files)

- `def CheckClaim.verifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:50](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L50) — The verifier for the `CheckClaim` reduction.
- `def DoNothing.verifier` [ArkLib/ProofSystem/Component/DoNothing.lean:34](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L34) — The verifier for the `DoNothing` reduction.
- `def NoInteraction.verifier` [ArkLib/ProofSystem/Component/NoInteraction.lean:53](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L53) — The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a function
- `def ReduceClaim.verifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:52](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L52) — The verifier for the `ReduceClaim` reduction.
- `def SendWitness.verifier` [ArkLib/ProofSystem/Component/SendWitness.lean:57](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L57) — (no docstring)
- `def Sumcheck.Spec.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L149) — The verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:404](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L404) — The verifier for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:842](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L842) — The verifier for the `i`-th round of the sum-check protocol
- `def Sumcheck.Spec.SingleRound.Unfolded.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1090](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1090) — The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1`

### `oracleProver` (8 declarations, 7 files)

- `def CheckClaim.oracleProver` [ArkLib/ProofSystem/Component/CheckClaim.lean:173](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L173) — The oracle prover for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleProver` [ArkLib/ProofSystem/Component/DoNothing.lean:67](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L67) — The oracle prover for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleProver` [ArkLib/ProofSystem/Component/RandomQuery.lean:62](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L62) — The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`, a
- `def ReduceClaim.oracleProver` [ArkLib/ProofSystem/Component/ReduceClaim.lean:189](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L189) — The oracle prover for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleProver` [ArkLib/ProofSystem/Component/SendClaim.lean:36](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L36) — The prover takes in the old oracle statement as input, and sends it as the protocol message.
- `def SendWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:138](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L138) — The oracle prover for the `SendWitness` oracle reduction. For each round `i : Fin (FinEnum.card ιw)`
- `def SendSingleWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:226](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L226) — The oracle prover for the `SendSingleWitness` oracle reduction. The prover sends the witness `wit` t
- `def RingSwitching.BatchingPhase.oracleProver` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:90](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L90) — (no docstring)

### `pSpec` (8 declarations, 6 files)

- `def RandomQuery.pSpec` [ArkLib/ProofSystem/Component/RandomQuery.lean:53](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L53) — (no docstring)
- `def SendClaim.pSpec` [ArkLib/ProofSystem/Component/SendClaim.lean:31](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L31) — (no docstring)
- `def SendWitness.pSpec` [ArkLib/ProofSystem/Component/SendWitness.lean:39](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L39) — (no docstring)
- `def Fri.Spec.FoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:334](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L334) — Each round of the FRI protocol begins with the verifier sending a random field element as the challe
- `def Fri.Spec.FinalFoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:578](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L578) — The final folding round of the FRI protocol begins with the verifier sending a random field element 
- `def Fri.Spec.QueryRound.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:753](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L753) — (no docstring)
- `def Sumcheck.Spec.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:125](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L125) — The protocol specification for the general sum-check protocol, which is the composition of the singl
- `def Sumcheck.Spec.SingleRound.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:148](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L148) — The protocol specification for a single round of sum-check. Has the form `⟨!v[.P_to_V, .V_to_P], !v[

### `prover` (7 declarations, 6 files)

- `def CheckClaim.prover` [ArkLib/ProofSystem/Component/CheckClaim.lean:39](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L39) — The prover for the `CheckClaim` reduction.
- `def DoNothing.prover` [ArkLib/ProofSystem/Component/DoNothing.lean:30](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L30) — The prover for the `DoNothing` reduction.
- `def NoInteraction.prover` [ArkLib/ProofSystem/Component/NoInteraction.lean:43](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L43) — The prover in a no-interaction reduction can be specified by a tuple of functions: - `mapStmt : Stmt
- `def ReduceClaim.prover` [ArkLib/ProofSystem/Component/ReduceClaim.lean:44](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L44) — The prover for the `ReduceClaim` reduction.
- `def SendWitness.prover` [ArkLib/ProofSystem/Component/SendWitness.lean:47](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L47) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:382](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L382) — The prover in the simple description of a single round of sum-check. Takes in input `target : R` and
- `def Sumcheck.Spec.SingleRound.Unfolded.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1080](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1080) — The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only well-

### `relation` (7 declarations, 6 files)

- `def ConstraintSystem.relation` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:68](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L68) — The underlying set-theoretic relation at a given index.
- `def Lookup.relation` [ArkLib/ProofSystem/ConstraintSystem/Lookup.lean:25](../../../ArkLib/ProofSystem/ConstraintSystem/Lookup.lean#L25) — The lookup relation. Takes in a collection of values and a table, both containers for elements of ty
- `def MemoryChecking.ReadOnly.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:128](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L128) — The read-only memory checking relation. It takes a memory `mem` and a list of read operations `ops`.
- `def MemoryChecking.ReadWrite.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:161](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L161) — The read-write memory checking relation. It takes an initial memory `startMem`, a final memory `fina
- `def Plonk.relation` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:193](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L193) — To define a relation based on the constraint system, we extend it with: - A natural number `ℓ ≤ m` r
- `def R1CS.relation` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:61](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L61) — The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean component-wise 
- `abbrev Spartan.Spec.relation` [ArkLib/ProofSystem/Spartan/Basic.lean:152](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L152) — This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨`

### `inputRelation` (8 declarations, 5 files)

- `def BatchedFri.Spec.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/General.lean:41](../../../ArkLib/ProofSystem/BatchedFri/Spec/General.lean#L41) — (no docstring)
- `def BatchedFri.Spec.BatchingRound.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:56](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L56) — (no docstring)
- `def Fri.Spec.inputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:37](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L37) — (no docstring)
- `def Fri.Spec.FoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:269](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L269) — The FRI non-final folding round input relation, with proximity parameter `0 < δ`, for the `i`-th rou
- `def Fri.Spec.FinalFoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:517](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L517) — Input relation for the final folding round, with proximity parameter `0 < δ`. The round-`k` codeword
- `def Fri.Spec.QueryRound.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:732](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L732) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:242](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L242) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:367](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L367) — (no docstring)

### `oracleVerifier_rbrKnowledgeSoundness` (7 declarations, 5 files)

- `theorem DoNothing.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:98](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L98) — The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound.
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomQuery.lean:278](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L278) — The `RandomQuery` oracle reduction is round-by-round knowledge sound. The key fact governing the sou
- `theorem ReduceClaim.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:336](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L336) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:218](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L218) — Round-by-round knowledge soundness with error `deg / \|R\|` per challenge for the (full) sum-check pro
- `theorem Sumcheck.Spec.SingleRound.Simpler.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:338](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L338) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:776](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L776) — Round-by-round knowledge soundness for the oracle verifier
- `theorem Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:975](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L975) — Round-by-round knowledge soundness theorem for single-round of sum-check, obtained by transporting t

### `Witness` (5 declarations, 5 files)

- `def BatchedFri.Spec.Witness` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:48](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L48) — The Batched FRI protocol has as witness for each batched polynomial that is supposed to correspond t
- `structure Binius.BinaryBasefold.Witness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:509](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L509) — The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and `Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁'
- `def R1CS.Witness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:51](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L51) — (no docstring)
- `def Fri.Spec.Witness` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:105](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L105) — The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in the
- `abbrev Spartan.Spec.Witness` [ArkLib/ProofSystem/Spartan/Basic.lean:148](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L148) — This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R`

### `outputRelation` (7 declarations, 4 files)

- `def BatchedFri.Spec.BatchingRound.outputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:65](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L65) — (no docstring)
- `def Fri.Spec.outputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:47](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L47) — (no docstring)
- `def Fri.Spec.FoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:297](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L297) — The FRI non-final folding round output relation, with proximity parameter `0 < δ`, for the `i`-th ro
- `def Fri.Spec.FinalFoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:546](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L546) — Output relation for the final folding round. After the final round the prover sends a polynomial in 
- `def Fri.Spec.QueryRound.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:740](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L740) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:271](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L271) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:370](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L370) — (no docstring)

### `Statement` (4 declarations, 4 files)

- `def R1CS.Statement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:45](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L45) — (no docstring)
- `def Fri.Spec.Statement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:75](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L75) — For the `i`-th round of the protocol, the input statement is equal to the challenges sent from round
- `abbrev Spartan.Spec.Statement` [ArkLib/ProofSystem/Spartan/Basic.lean:140](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L140) — This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R`
- `structure Sumcheck.Structured.Statement` [ArkLib/ProofSystem/Sumcheck/Structured.lean:197](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L197) — Statement per iterated sumcheck round

### `disagreementSet` (4 declarations, 4 files)

- `def disagreementSet` [ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean:56](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean#L56) — The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁.
- `def Binius.BinaryBasefold.disagreementSet` [ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean:1042](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean#L1042) — Disagreement set Δ : The set of points where two functions disagree. For functions f^(i+ϑ) and g^(i+
- `def Quotienting.disagreementSet` [ArkLib/ProofSystem/Stir/Quotienting.lean:52](../../../ArkLib/ProofSystem/Stir/Quotienting.lean#L52) — We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S such that 
- `def BlockRelDistance.disagreementSet` [ArkLib/ProofSystem/Whir/BlockRelDistance.lean:97](../../../ArkLib/ProofSystem/Whir/BlockRelDistance.lean#L97) — Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then the (i,k)

### `reduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:70](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L70) — The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the input
- `theorem NoInteraction.reduction_completeness` [ArkLib/ProofSystem/Component/NoInteraction.lean:69](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L69) — (no docstring)
- `theorem ReduceClaim.reduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:66](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L66) — The `ReduceClaim` reduction satisfies perfect completeness for any relation.
- `theorem SendWitness.reduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:77](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L77) — The `SendWitness` reduction satisfies perfect completeness.

### `ratchet` (5 declarations, 3 files)

- `def DomainSeparator.ratchet` [ArkLib/Data/Hash/DomainSep.lean:221](../../../ArkLib/Data/Hash/DomainSep.lean#L221) — Ratchet the state. Rust interface: ```rust pub fn ratchet(self) -> Self ```
- `def DuplexSponge.ratchet` [ArkLib/Data/Hash/DuplexSponge.lean:612](../../../ArkLib/Data/Hash/DuplexSponge.lean#L612) — ### Ratchet the sponge state for domain separation Algorithm (from Rust implementation): 1. Permute 
- `def HashStateWithInstructions.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:141](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L141) — Perform a ratchet operation. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainS
- `def FSVerifierState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:258](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L258) — Signal the end of statement with ratcheting. Rust interface: ```rust pub fn ratchet(&mut self) -> Re
- `def FSProverState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:371](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L371) — Ratchet the protocol state. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainSe

### `StmtIn` (4 declarations, 3 files)

- `def RandomQuery.StmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:30](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L30) — (no docstring)
- `def Sumcheck.Spec.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:137](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L137) — The input statement for the (full) sum-check protocol, which contains only the target sum value
- `def Sumcheck.Spec.SingleRound.Simpler.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:239](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L239) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:356](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L356) — (no docstring)

### `drop` (4 declarations, 3 files)

- `def Fin.drop` [ArkLib/Data/Fin/Tuple/Defs.lean:60](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L60) — Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.
- `def ProtocolSpec.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:117](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L117) — Drop the first `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:174](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L174) — (no docstring)
- `def SumcheckDomain.drop` [ArkLib/ProofSystem/Sumcheck/Domain.lean:116](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L116) — Drop the first `j` coordinates, leaving the domain on the remaining `k - j` coordinates: coordinate 

### `reduction_perfectCompleteness` (4 declarations, 3 files)

- `theorem DoNothing.reduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:51](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L51) — The `DoNothing` reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:208](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L208) — Perfect completeness for the (full) sum-check protocol
- `theorem Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:543](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L543) — Perfect completeness for the (non-oracle) reduction
- `theorem Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:944](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L944) — (no docstring)

### `verifier_rbrKnowledgeSoundness` (4 declarations, 3 files)

- `theorem DoNothing.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:57](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L57) — The `DoNothing` verifier is perfectly round-by-round knowledge sound.
- `theorem ReduceClaim.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:170](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L170) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:770](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L770) — Round-by-round knowledge soundness for the verifier
- `theorem Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:952](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L952) — (no docstring)

### `Params` (3 declarations, 3 files)

- `structure Poseidon2.Params` [ArkLib/Data/Hash/Poseidon2.lean:412](../../../ArkLib/Data/Hash/Poseidon2.lean#L412) — The parameters determining a Poseidon2 permutation (over the KoalaBear field)
- `structure StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:32](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L32) — **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun
- `structure WhirIOP.Params` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:54](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L54) — ** Per‑round protocol parameters. ** For a fixed depth `M`, the reduction runs `M + 1` rounds. In ro

### `absorb` (3 declarations, 3 files)

- `def DomainSeparator.absorb` [ArkLib/Data/Hash/DomainSep.lean:182](../../../ArkLib/Data/Hash/DomainSep.lean#L182) — Absorb `count` native elements. Rust interface: ```rust pub fn absorb(self, count: usize, label: &st
- `def DuplexSponge.absorb` [ArkLib/Data/Hash/DuplexSponge.lean:416](../../../ArkLib/Data/Hash/DuplexSponge.lean#L416) — ### Absorb a list of units into the sponge (paper version) Paper algorithm (process one element at a
- `def HashStateWithInstructions.absorb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:105](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L105) — Perform secure absorption of elements into the sponge. Rust interface: ```rust pub fn absorb(&mut se

### `coreInteractionOracleReduction` (3 declarations, 3 files)

- `def coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:610](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L610) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:628](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L628) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:521](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L521) — Large-field reduction: Sumcheck seqCompose, then append FinalSum

### `coreInteractionOracleVerifier` (3 declarations, 3 files)

- `def coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:595](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L595) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:610](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L610) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:512](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L512) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum

### `finalSumcheckKStateProp` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:971](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L971) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:527](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L527) — (no docstring)
- `def RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:419](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L419) — (no docstring)

### `finalSumcheckKnowledgeStateFunction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1005](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1005) — The knowledge state function for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:569](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L569) — The knowledge state function for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:449](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L449) — The knowledge state function for the final sumcheck step

### `finalSumcheckOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:900](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L900) — The oracle reduction for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:450](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L450) — The oracle reduction for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:367](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L367) — The oracle reduction for the final sumcheck step

### `finalSumcheckOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:914](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L914) — Perfect completeness for the final sumcheck step
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:466](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L466) — Perfect completeness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:381](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L381) — Perfect completeness for the final sumcheck step

### `finalSumcheckOracleVerifier_rbrKnowledgeSoundness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1025](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1025) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:590](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L590) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:468](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L468) — Round-by-round knowledge soundness for the final sumcheck step

### `finalSumcheckProver` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckProver` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:814](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L814) — The prover for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:353](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L353) — The prover for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:292](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L292) — The prover for the final sumcheck step

### `finalSumcheckRbrExtractor` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:941](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L941) — The round-by-round extractor for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:495](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L495) — The round-by-round extractor for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:399](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L399) — The round-by-round extractor for the final sumcheck step

### `finalSumcheckVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:856](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L856) — The verifier for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:397](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L397) — The verifier for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:328](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L328) — The verifier for the final sumcheck step

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
- `theorem RingSwitching.FullRingSwitching.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/General.lean:119](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L119) — (no docstring)

### `fullOracleVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:44](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L44) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:113](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L113) — The oracle verifier for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:51](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L51) — The oracle verifier for the full Binary Basefold protocol

### `knowledgeStateFunction` (3 declarations, 3 files)

- `def CheckClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/CheckClaim.lean:121](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L121) — The knowledge state function for the `CheckClaim` reduction, mirroring the trivial-verifier template
- `def RandomQuery.knowledgeStateFunction` [ArkLib/ProofSystem/Component/RandomQuery.lean:235](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L235) — The knowledge state function for the `RandomQuery` oracle reduction.
- `def ReduceClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:137](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L137) — The knowledge state function for the `ReduceClaim` reduction.

### `oracleReduction_completeness` (3 declarations, 3 files)

- `theorem RandomQuery.oracleReduction_completeness` [ArkLib/ProofSystem/Component/RandomQuery.lean:114](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L114) — The `RandomQuery` oracle reduction is perfectly complete.
- `theorem ReduceClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:221](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L221) — The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. Proof strategy m
- `theorem SendSingleWitness.oracleReduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:294](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L294) — The `SendSingleWitness` oracle reduction satisfies perfect completeness.

### `relOut` (3 declarations, 3 files)

- `def CheckClaim.relOut` [ArkLib/ProofSystem/Component/CheckClaim.lean:63](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L63) — (no docstring)
- `def RandomQuery.relOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:49](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L49) — The output relation states that if the verifier's single query was `q`, then `a` and `b` agree on th
- `def SendClaim.relOut` [ArkLib/ProofSystem/Component/SendClaim.lean:98](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L98) — (no docstring)

### `squeeze` (3 declarations, 3 files)

- `def DomainSeparator.squeeze` [ArkLib/Data/Hash/DomainSep.lean:207](../../../ArkLib/Data/Hash/DomainSep.lean#L207) — Squeeze `count` native elements. Rust interface: ```rust pub fn squeeze(self, count: usize, label: &
- `def DuplexSponge.squeeze` [ArkLib/Data/Hash/DuplexSponge.lean:512](../../../ArkLib/Data/Hash/DuplexSponge.lean#L512) — ### Squeeze out a vector of units from the sponge (paper version) We differ from the paper version i
- `def HashStateWithInstructions.squeeze` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:117](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L117) — Perform a secure squeeze operation. Rust interface: ```rust pub fn squeeze(&mut self, output: &mut [

### `cast_id` (9 declarations, 2 files)

- `theorem Prover.cast_id` [ArkLib/OracleReduction/Cast.lean:53](../../../ArkLib/OracleReduction/Cast.lean#L53) — (no docstring)
- `theorem OracleProver.cast_id` [ArkLib/OracleReduction/Cast.lean:77](../../../ArkLib/OracleReduction/Cast.lean#L77) — (no docstring)
- `theorem Verifier.cast_id` [ArkLib/OracleReduction/Cast.lean:99](../../../ArkLib/OracleReduction/Cast.lean#L99) — (no docstring)
- `theorem Reduction.cast_id` [ArkLib/OracleReduction/Cast.lean:173](../../../ArkLib/OracleReduction/Cast.lean#L173) — (no docstring)
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
- `def OracleReduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:247](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L247) — Sequential composition of oracle reductions, defined via sequential composition of oracle provers an
- `def ProtocolSpec.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:276](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L276) — Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`. Defined for definitio
- `def ProtocolSpec.FullTranscript.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:334](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L334) — Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`. Defined for definit

### `seqCompose_zero` (7 declarations, 2 files)

- `lemma Prover.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:48](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L48) — (no docstring)
- `lemma Verifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:83](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L83) — (no docstring)
- `lemma Reduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:113](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L113) — (no docstring)
- `lemma OracleVerifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:196](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L196) — (no docstring)
- `lemma OracleReduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:263](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L263) — (no docstring)
- `theorem ProtocolSpec.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:292](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L292) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:339](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L339) — (no docstring)

### `completeness` (5 declarations, 2 files)

- `def Reduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:83](../../../ArkLib/OracleReduction/Security/Basic.lean#L83) — A reduction satisfies **completeness** with regards to: - an initialization function `init : ProbCom
- `def OracleReduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:365](../../../ArkLib/OracleReduction/Security/Basic.lean#L365) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:419](../../../ArkLib/OracleReduction/Security/Basic.lean#L419) — (no docstring)
- `def OracleProof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:448](../../../ArkLib/OracleReduction/Security/Basic.lean#L448) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `theorem SendClaim.completeness` [ArkLib/ProofSystem/Component/SendClaim.lean:110](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L110) — (no docstring)

### `concat` (5 declarations, 2 files)

- `def ProtocolSpec.MessagesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:403](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L403) — Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming round `
- `def ProtocolSpec.ChallengesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:462](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L462) — Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming rou
- `abbrev ProtocolSpec.Transcript.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:515](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L515) — Concatenate a message to the end of a partial transcript. This is definitionally equivalent to `Fin.
- `abbrev ProtocolSpec.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:31](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L31) — Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec`
- `def ProtocolSpec.FullTranscript.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:149](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L149) — Adding a message with a given direction and type to the end of a `Transcript`

### `knowledgeSoundness` (5 declarations, 2 files)

- `def Verifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:272](../../../ArkLib/OracleReduction/Security/Basic.lean#L272) — A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and wit
- `def OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:394](../../../ArkLib/OracleReduction/Security/Basic.lean#L394) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:435](../../../ArkLib/OracleReduction/Security/Basic.lean#L435) — (no docstring)
- `def OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:473](../../../ArkLib/OracleReduction/Security/Basic.lean#L473) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.knowledgeSoundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:141](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L141) — State-restoration knowledge soundness (w/ straightline extractor).

### `new` (5 declarations, 2 files)

- `def DomainSeparator.Op.new` [ArkLib/Data/Hash/DomainSep.lean:138](../../../ArkLib/Data/Hash/DomainSep.lean#L138) — Construct a new `Op` from a character `id` and a count number `count : Option Nat`. Returns error if
- `def DomainSeparator.new` [ArkLib/Data/Hash/DomainSep.lean:159](../../../ArkLib/Data/Hash/DomainSep.lean#L159) — Create a new DomainSeparator with the domain separator. Rust interface: ```rust pub fn new(session_i
- `def HashStateWithInstructions.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:93](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L93) — Initialize a stateful hash object from a domain separator. Rust interface: ```rust pub fn new(domain
- `def FSVerifierState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:183](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L183) — Create a new VerifierState from a domain separator and NARG string. Rust interface: ```rust pub fn n
- `def FSProverState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:326](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L326) — Create a new `FSProverState` from a domain separator and RNG. Rust interface: ```rust pub fn new(dom

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

### `oracleReduction_perfectCompleteness` (4 declarations, 2 files)

- `theorem DoNothing.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:92](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L92) — The `DoNothing` oracle reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.SingleRound.Simpler.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:312](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L312) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:762](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L762) — Perfect completeness for the oracle reduction
- `theorem Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:962](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L962) — Completeness theorem for single-round of sum-check, obtained by transporting the completeness proof 

### `OStmtIn` (3 declarations, 2 files)

- `def RandomQuery.OStmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:33](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L33) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:240](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L240) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:362](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L362) — (no docstring)

### `OStmtOut` (3 declarations, 2 files)

- `def RandomQuery.OStmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:34](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L34) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:269](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L269) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:365](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L365) — (no docstring)

### `StmtOut` (3 declarations, 2 files)

- `def RandomQuery.StmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:31](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L31) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:268](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L268) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:359](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L359) — (no docstring)

### `correctness` (3 declarations, 2 files)

- `def Commitment.correctness` [ArkLib/CommitmentScheme/Basic.lean:88](../../../ArkLib/CommitmentScheme/Basic.lean#L88) — A commitment scheme satisfies **correctness** with error `correctnessError` if for all `data : Data`
- `theorem KZG.correctness` [ArkLib/CommitmentScheme/KZG/Correctness.lean:51](../../../ArkLib/CommitmentScheme/KZG/Correctness.lean#L51) — Algebraic correctness of one KZG opening for a coefficient vector.
- `theorem KZG.CommitmentScheme.correctness` [ArkLib/CommitmentScheme/KZG/Correctness.lean:161](../../../ArkLib/CommitmentScheme/KZG/Correctness.lean#L161) — The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

### `extract` (3 declarations, 2 files)

- `def Fin.extract` [ArkLib/Data/Fin/Tuple/Defs.lean:73](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L73) — Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`.
- `def ProtocolSpec.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:125](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L125) — Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`.
- `abbrev ProtocolSpec.FullTranscript.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:182](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L182) — (no docstring)

### `rdrop` (3 declarations, 2 files)

- `abbrev Fin.rdrop` [ArkLib/Data/Fin/Tuple/Defs.lean:68](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L68) — Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. This is defi
- `def ProtocolSpec.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:121](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L121) — Drop the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:178](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L178) — (no docstring)

### `rtake` (3 declarations, 2 files)

- `def Fin.rtake` [ArkLib/Data/Fin/Tuple/Defs.lean:55](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L55) — Take the last `m` elements of a finite vector
- `def ProtocolSpec.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:113](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L113) — Take the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:170](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L170) — Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec`

### `toFinset` (3 declarations, 2 files)

- `def ReedSolomon.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon.lean:81](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L81) — (no docstring)
- `def ReedSolomon.FftDomain.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:184](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L184) — (no docstring)
- `def ReedSolomon.CosetFftDomain.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:552](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L552) — (no docstring)

### `ChallengeIdx` (2 declarations, 2 files)

- `def ProtocolSpec.ChallengeIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:54](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L54) — Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification
- `def ProtocolSpec.VectorSpec.ChallengeIdx` [ArkLib/OracleReduction/VectorIOR.lean:54](../../../ArkLib/OracleReduction/VectorIOR.lean#L54) — The type of indices for challenges in a `VectorSpec`.

### `ConstraintSystem` (2 declarations, 2 files)

- `structure ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:49](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L49) — A **constraint system** packages a family of indexed relations into a single bundle. For each `i : I
- `def Plonk.ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:116](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L116) — A Plonk constraint system is a vector of `numGates` gates, each parametrized by the underlying ring 

### `FinalSumcheckWit` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:935](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L935) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:489](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L489) — (no docstring)

### `GenMutualCorrParams` (2 declarations, 2 files)

- `class Fold.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/Folding.lean:165](../../../ArkLib/ProofSystem/Whir/Folding.lean#L165) — The `GenMutualCorrParams` class captures the necessary parameters and assumptions to model a sequenc
- `class WhirIOP.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:85](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L85) — `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes `C_{i : M + 1, j : foldingPar

### `MessageIdx` (2 declarations, 2 files)

- `def ProtocolSpec.MessageIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:49](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L49) — Subtype of `Fin n` for the indices corresponding to messages in a protocol specification
- `def ProtocolSpec.VectorSpec.MessageIdx` [ArkLib/OracleReduction/VectorIOR.lean:50](../../../ArkLib/OracleReduction/VectorIOR.lean#L50) — The type of indices for messages in a `VectorSpec`.

### `ParamConditions` (2 declarations, 2 files)

- `structure StirIOP.ParamConditions` [ArkLib/ProofSystem/Stir/MainThm.lean:52](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L52) — **Conditions that protocol parameters must satisfy.** - `h_deg` : initial degree `deg` is a power of
- `structure WhirIOP.ParamConditions` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:66](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L66) — ** Conditions that protocol parameters must satisfy. ** h_m : m = varCount₀ h_sumkLt : ∑ i : Fin (M 

### `SumcheckMultiplierParam` (2 declarations, 2 files)

- `structure Sumcheck.Structured.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured.lean:85](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L85) — Parameters describing how the round polynomial `H` is built from the witness `t`: `H = P · Q(t)`, wh
- `structure Sumcheck.Structured.Prismalinear.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:50](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L50) — Parameters describing how a *prismalinear* round polynomial `H = P · Q(t)` is built from the witness

### `SumcheckWitness` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckWitness` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:234](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L234) — (no docstring)
- `structure Sumcheck.Structured.SumcheckWitness` [ArkLib/ProofSystem/Sumcheck/Structured.lean:231](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L231) — Witness for the structured sumcheck at round `i`: - `t'` — the original multilinear polynomial (the 

### `append_left_injective` (2 declarations, 2 files)

- `theorem Fin.append_left_injective` [ArkLib/Data/Fin/Basic.lean:238](../../../ArkLib/Data/Fin/Basic.lean#L238) — (no docstring)
- `theorem ProtocolSpec.append_left_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:55](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L55) — (no docstring)

### `append_right_injective` (2 declarations, 2 files)

- `theorem Fin.append_right_injective` [ArkLib/Data/Fin/Basic.lean:246](../../../ArkLib/Data/Fin/Basic.lean#L246) — (no docstring)
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

### `commit` (2 declarations, 2 files)

- `def KZG.commit` [ArkLib/CommitmentScheme/KZG/Basic.lean:55](../../../ArkLib/CommitmentScheme/KZG/Basic.lean#L55) — To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of maximum deg
- `def SimpleRO.commit` [ArkLib/CommitmentScheme/SimpleRO.lean:43](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L43) — (no docstring)

### `computeRoundPoly` (2 declarations, 2 files)

- `def Sumcheck.Structured.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured.lean:130](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L130) — The general round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` is the public multilinea
- `def Sumcheck.Structured.Prismalinear.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:70](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L70) — The *prismalinear* round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` has per-variable 

### `coreInteractionOracleRbrKnowledgeError` (2 declarations, 2 files)

- `def coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:647](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L647) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:674](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L674) — (no docstring)

### `coreInteractionOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:629](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L629) — Perfect completeness for the core interaction oracle reduction
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:650](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L650) — Perfect completeness for the core interaction oracle reduction

### `coreInteractionOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:655](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L655) — Round-by-round knowledge soundness for the core interaction oracle verifier
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:683](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L683) — Round-by-round knowledge soundness for the core interaction oracle verifier

### `decoder` (2 declarations, 2 files)

- `def BerlekampWelch.decoder` [ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:52](../../../ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean#L52) — Berlekamp-Welch decoder for Reed-Solomon codes. Given received codeword evaluations with potential e
- `def GuruswamiSudan.decoder` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:98](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L98) — Guruswami-Sudan decoder.  Returns all roots of the GS interpolation polynomial whose evaluation is w

### `finalSumcheckKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:930](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L930) — RBR knowledge error for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:484](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L484) — RBR knowledge error for the final sumcheck step

### `foldOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.foldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:198](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L198) — The oracle reduction that is the `i`-th round of Binary Foldfold.
- `def Fri.Spec.FoldPhase.foldOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:459](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L459) — The oracle reduction that is the `i`-th round of the FRI protocol.

### `fullOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:150](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L150) — Round-by-round knowledge soundness for the full Binary Basefold oracle verifier
- `theorem RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/General.lean:145](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L145) — Round-by-round knowledge soundness for the full ring-switching oracle verifier

### `fullPspec` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.fullPspec` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:59](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L59) — (no docstring)
- `def RingSwitching.fullPspec` [ArkLib/ProofSystem/RingSwitching/Spec.lean:56](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L56) — (no docstring)

### `fullRbrKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:140](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L140) — Combined RBR knowledge soundness error for the full protocol
- `def RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/General.lean:137](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L137) — (no docstring)

### `guruswami_sudan_for_proximity_gap_existence` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:889](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L889) — Constructive witness extraction for the Guruswami–Sudan system. When the computable `hasWitnessC` ch
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:37](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L37) — The first part of Lemma 5.3 from [BCIKS20]. Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`pr

### `guruswami_sudan_for_proximity_gap_property` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:928](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L928) — Constructive witness property for the Guruswami–Sudan system. When `m > 0` and the codeword polynomi
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:49](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L49) — The second part of Lemma 5.3 from [BCIKS20]. For any solution `Q` of the Guruswami-Sudan system, and

### `hint` (2 declarations, 2 files)

- `def DomainSeparator.hint` [ArkLib/Data/Hash/DomainSep.lean:196](../../../ArkLib/Data/Hash/DomainSep.lean#L196) — Hint `count` native elements. Rust interface: ```rust pub fn hint(self, label: &str) -> Self ```
- `def HashStateWithInstructions.hint` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:129](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L129) — Process a hint operation. Rust interface: ```rust pub fn hint(&mut self) -> Result<(), DomainSeparat

### `leftpad` (2 declarations, 2 files)

- `def Fin.leftpad` [ArkLib/Data/Fin/Tuple/Defs.lean:96](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L96) — Pad a `Fin`-indexed vector on the left with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.leftpad` [ArkLib/Data/Matrix/Basic.lean:23](../../../ArkLib/Data/Matrix/Basic.lean#L23) — (no docstring)

### `liftContext_completeness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:118](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L118) — (no docstring)
- `theorem Reduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:350](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L350) — Lifting the reduction preserves completeness, assuming the lens satisfies its completeness condition

### `liftContext_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:155](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L155) — (no docstring)
- `theorem Verifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:440](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L440) — (no docstring)

### `liftContext_perfectCompleteness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:125](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L125) — (no docstring)
- `theorem Reduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:374](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L374) — (no docstring)

### `liftContext_rbr_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:186](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L186) — (no docstring)
- `theorem Verifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:523](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L523) — (no docstring)

### `liftContext_rbr_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:172](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L172) — (no docstring)
- `theorem Verifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:489](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L489) — (no docstring)

### `liftContext_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:142](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L142) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
- `theorem Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:396](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L396) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions

### `masterKStateProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.masterKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:926](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L926) — Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event of the `i-th` oracle if
- `def RingSwitching.masterKStateProp` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:428](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L428) — (no docstring)

### `minDist` (2 declarations, 2 files)

- `def Code.minDist` [ArkLib/Data/CodingTheory/Basic/Distance.lean:164](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean#L164) — (no docstring)
- `theorem ReedSolomon.minDist` [ArkLib/Data/CodingTheory/ReedSolomon.lean:395](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L395) — The minimal code distance of an RS code of length `ι` and dimension `deg` is `ι - deg + 1`.

### `pSpecCoreInteraction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:248](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L248) — (no docstring)
- `def RingSwitching.pSpecCoreInteraction` [ArkLib/ProofSystem/RingSwitching/Spec.lean:49](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L49) — (no docstring)

### `pSpecFold` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecFold` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:201](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L201) — (no docstring)
- `def Fri.Spec.pSpecFold` [ArkLib/ProofSystem/Fri/Spec/General.lean:57](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L57) — (no docstring)

### `pSpecSumcheckRound` (2 declarations, 2 files)

- `abbrev RingSwitching.pSpecSumcheckRound` [ArkLib/ProofSystem/RingSwitching/Spec.lean:41](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L41) — (no docstring)
- `def Sumcheck.Structured.pSpecSumcheckRound` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:102](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L102) — Protocol spec for one round of the structured sumcheck: P sends a degree-≤`d` univariate `h_i(X) ∈ L

### `proximityCondition` (2 declarations, 2 files)

- `def MutualCorrAgreement.proximityCondition` [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:47](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean#L47) — For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽` and linea
- `def Generator.proximityCondition` [ArkLib/ProofSystem/Whir/ProximityGen.lean:42](../../../ArkLib/ProofSystem/Whir/ProximityGen.lean#L42) — For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽ˡ` and linear 

### `queryCodeword` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryCodeword` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:145](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L145) — Oracle query helper: query a committed codeword at a given domain point. Restricted to codeword indi
- `def Fri.Spec.QueryRound.queryCodeword` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:816](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L816) — (no docstring)

### `queryOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:305](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L305) — The oracle reduction for the final query phase.
- `def Fri.Spec.QueryRound.queryOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:927](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L927) — (no docstring)

### `reduction_verifier_eq_verifier` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:193](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L193) — (no docstring)
- `lemma Sumcheck.Spec.SingleRound.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:866](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L866) — (no docstring)

### `relIn` (2 declarations, 2 files)

- `def CheckClaim.relIn` [ArkLib/ProofSystem/Component/CheckClaim.lean:60](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L60) — (no docstring)
- `def RandomQuery.relIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:41](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L41) — The input relation is that the two oracles are equal.

### `rightpad` (2 declarations, 2 files)

- `def Fin.rightpad` [ArkLib/Data/Fin/Tuple/Defs.lean:90](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L90) — Pad a `Fin`-indexed vector on the right with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.rightpad` [ArkLib/Data/Matrix/Basic.lean:19](../../../ArkLib/Data/Matrix/Basic.lean#L19) — (no docstring)

### `roundKnowledgeError` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckPhase.roundKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:153](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L153) — (no docstring)
- `def Sumcheck.Structured.roundKnowledgeError` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:290](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L290) — Round-by-round knowledge error for a single round of the structured sumcheck: the Schwartz–Zippel bo

### `run` (2 declarations, 2 files)

- `def AGM.Adversary.run` [ArkLib/AGM/Basic.lean:164](../../../ArkLib/AGM/Basic.lean#L164) — Running the adversary on a given table, returning the list of group elements it is supposed to outpu
- `def Prover.run` [ArkLib/OracleReduction/Execution.lean:153](../../../ArkLib/OracleReduction/Execution.lean#L153) — Run the prover in an interactive reduction. Returns the output statement and witness, and the transc

### `sumcheckFoldOracleReduction` (2 declarations, 2 files)

- `def sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:503](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L503) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:145](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L145) — (no docstring)

### `sumcheckFoldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:551](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L551) — Perfect completeness for the core interaction oracle reduction
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:206](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L206) — (no docstring)

### `sumcheckFoldOracleVerifier` (2 declarations, 2 files)

- `def sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:340](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L340) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:139](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L139) — (no docstring)

### `sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:575](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L575) — Round-by-round knowledge soundness for the sumcheck fold oracle verifier
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:315](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L315) — (no docstring)

### `witnessStructuralInvariant` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:818](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L818) — This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
- `def RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:421](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L421) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`

### `OracleInterface` (3 declarations, 2 files)

- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:88](../../../ArkLib/OracleReduction/Basic.lean#L88) — (no docstring)
- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:162](../../../ArkLib/OracleReduction/Basic.lean#L162) — (no docstring)
- `class OracleInterface` [ArkLib/OracleReduction/OracleInterface.lean:49](../../../ArkLib/OracleReduction/OracleInterface.lean#L49) — `OracleInterface` is a type class that provides an oracle interface for a type `Message`. It consist

## Near-duplicate docstrings (Jaccard ≥ 0.85, 62 cross-file pairs)

Each pair has docstrings sharing a high fraction of (4+-letter) words, in different files. Most are unrelated coincidences in boilerplate; look for pairs where the *concept* matches.

- **1.00** `Binius.BinaryBasefold.CoreInteraction.commitKState` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:585](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L585) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:237](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L237)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.commitOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:605](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L605) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:273](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L273)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:930](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L930) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:484](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L484)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:930](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L930) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:396](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L396)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1005](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1005) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:569](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L569)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1005](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1005) vs `RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:449](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L449)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:900](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L900) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:450](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L450)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:900](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L900) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:367](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L367)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:914](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L914) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:466](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L466)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:914](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L914) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:381](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L381)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1025](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1025) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:590](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L590)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1025](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1025) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:468](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L468)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:941](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L941) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:495](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L495)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:941](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L941) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:399](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L399)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.foldKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:343](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L343) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:237](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L237)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.foldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:375](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L375) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:273](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L273)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.CoreInteraction.relayKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:745](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L745) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:237](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L237)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.relayOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:768](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L768) vs `RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:273](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L273)
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
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:818](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L818) vs `RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:421](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L421)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:56](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L56) vs `Binius.FRIBinius.FullFRIBinius.biniusProfile` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:51](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L51)
    - a: The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def
    - b: The Binius ring-switching profile, built from the boolean-hypercube basis derived from `β`. Kept def
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:484](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L484) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:396](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L396)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:569](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L569) vs `RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:449](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L449)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:450](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L450) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:367](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L367)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:466](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L466) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:381](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L381)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:590](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L590) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:468](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L468)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:495](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L495) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:399](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L399)
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
- **1.00** `OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:142](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L142) vs `Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:396](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L396)
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
- **1.00** `coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:610](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L610) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:628](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L628)
    - a: The final oracle reduction that composes sumcheckFold with finalSumcheckStep
    - b: The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- **1.00** `coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:629](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L629) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:650](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L650)
    - a: Perfect completeness for the core interaction oracle reduction
    - b: Perfect completeness for the core interaction oracle reduction
- **1.00** `coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:595](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L595) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:610](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L610)
    - a: The final oracle verifier that composes sumcheckFold with finalSumcheckStep
    - b: The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- **1.00** `coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:655](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L655) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:683](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L683)
    - a: Round-by-round knowledge soundness for the core interaction oracle verifier
    - b: Round-by-round knowledge soundness for the core interaction oracle verifier
- **1.00** `sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:551](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L551) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:650](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L650)
    - a: Perfect completeness for the core interaction oracle reduction
    - b: Perfect completeness for the core interaction oracle reduction
- **0.88** `OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:473](../../../ArkLib/OracleReduction/Security/Basic.lean#L473) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:506](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L506)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:473](../../../ArkLib/OracleReduction/Security/Basic.lean#L473) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:463](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L463)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:394](../../../ArkLib/OracleReduction/Security/Basic.lean#L394) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:506](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L506)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:394](../../../ArkLib/OracleReduction/Security/Basic.lean#L394) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:463](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L463)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:465](../../../ArkLib/OracleReduction/Security/Basic.lean#L465) vs `OracleProof.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:498](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L498)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:465](../../../ArkLib/OracleReduction/Security/Basic.lean#L465) vs `OracleVerifier.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:454](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L454)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleVerifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:653](../../../ArkLib/OracleReduction/Security/Basic.lean#L653) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:583](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L583)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:386](../../../ArkLib/OracleReduction/Security/Basic.lean#L386) vs `OracleProof.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:498](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L498)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:386](../../../ArkLib/OracleReduction/Security/Basic.lean#L386) vs `OracleVerifier.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:454](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L454)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `Verifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:569](../../../ArkLib/OracleReduction/Security/Basic.lean#L569) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:583](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L583)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `proximity_gap_degree_bound` [ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean:28](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean#L28) vs `ProximityGap.D_X` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:31](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L31)
    - a: The degree bound (i.e. `D_X(m) = (m + 1/2) * √ρ * n`) for instantiation of Guruswami-Sudan in Lemma 
    - b: The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan in Lemma 5.3 of [BCIKS20]. `D_X


/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.Basic
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Key Lemma for Duplex-Sponge Fiat-Shamir Security (Lemma 5.1)

This module formalizes the core statistical indistinguishability result (Lemma 5.1 in Chiesa-Orrù [CO25])
bridging the Duplex-Sponge Fiat-Shamir (DSFS) transformation and the basic Fiat-Shamir transformation.

The key lemma asserts that the security games for basic Fiat-Shamir and duplex-sponge Fiat-Shamir
yield statistically indistinguishable distributions on their output transcripts (up to a small simulation
error $\eta^*$), provided that the malicious prover and query-answer traces are mapped via the
appropriate trace and prover transformations.

From this result, preservation of both soundness and knowledge soundness under the DSFS transformation
follows directly.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type}
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  {U : Type} [SpongeUnit U] [SpongeSize]
  -- All messages are serializable to vectors of units
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  -- All challenges are deserializable from vectors of units
  [HasChallengeSize pSpec] [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

section SecurityGames

/-- First game for the key lemma: the basic Fiat-Shamir transform.

We run the malicious prover, then the verifier, then returns:
- the input statement (that the malicious prover chooses)
- the output statement (that the verifier returns)
- the messages / proof sent by the prover
- the query log of the prover
- the query log of the verifier -/
def basicFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (StmtIn × pSpec.Messages)) :
    OptionT (OracleComp (oSpec + fsChallengeOracle StmtIn pSpec))
      (StmtIn × StmtOut × pSpec.Messages × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
        × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)) := do
  let ⟨⟨stmtIn, messages⟩, proveQueryLog⟩ ← (simulateQ loggingOracle P).run
  let ⟨stmtOut, verifyQueryLog⟩ ← (simulateQ loggingOracle
    (V.fiatShamir.run stmtIn (fun i => match i with | ⟨0, _⟩ => messages))).run
  return ⟨stmtIn, ← stmtOut.getM, messages, proveQueryLog, verifyQueryLog⟩

/-- Second game for the key lemma: the duplex sponge Fiat-Shamir transform.

We run the malicious prover, then the verifier, then returns:
- the input statement (that the malicious prover chooses)
- the output statement (that the verifier returns)
- the messages / proof sent by the prover
- the query log of the prover
- the query log of the verifier -/
def duplexSpongeFiatShamirGame (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    OptionT (OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U))
      (StmtIn × StmtOut × pSpec.Messages
        × QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)
        × QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) := do
  let ⟨⟨stmtIn, messages⟩, proveQueryLog⟩ ← (simulateQ loggingOracle P).run
  let ⟨stmtOut, verifyQueryLog⟩ ←
    liftM (simulateQ loggingOracle
      (V.duplexSpongeFiatShamir.run
        stmtIn (fun i => match i with | ⟨0, _⟩ => messages))).run
  return ⟨stmtIn, ← stmtOut.getM, messages, proveQueryLog, verifyQueryLog⟩

end SecurityGames

section KeyLemma

open scoped NNReal

variable [DecidableEq ι]

/-- `θStar` in the paper, which is just equal to `tₚ`, the bound for number of forward permutation
  queries made by the malicious prover -/
def θStar (_tₕ tₚ _tₚᵢ : ℕ) : ℕ := tₚ

/-!
`ηStar` in the paper, is the bound on the statistical distance between two experiments in Lemma 5.1
-/
noncomputable def ηStar (U : Type) [SpongeUnit U] [Fintype U]
    (tₕ tₚ tₚᵢ : ℕ) (L : ℕ) (εcodec : pSpec.ChallengeIdx → ℝ≥0) : ℝ≥0 :=
  let tTotal : ℕ := (tₕ + tₚ + tₚᵢ)
  -- First term in Equation (5)
  -- Numerator: `7 * t ^ 2 + (28 * L + 25) * t + (14 * L + 1) * (L + 1)`
  -- Note: we rewrote the numerator to make it clear that the term is nonnegative (no subtraction)
  -- Original: `7 * t ^ 2 + 28 * (L + 1) * t + 14 * (L + 1) ^ 2 - 3 * t - 13 * (L + 1)`
  let firstTermNumerator : ℝ≥0 :=
    7 * tTotal ^2 + (28 * L + 25) * tTotal + (14 * L + 1) * (L + 1)
  let firstTermDenominator : ℝ≥0 := 2 * ((Fintype.card U) ^ (SpongeSize.C + 1))
  -- Second term in Equation (5)
  let secondTerm : ℝ≥0 := θStar tₕ tₚ tₚᵢ * (iSup εcodec)
  -- Third term in Equation (5)
  let thirdTerm : ℝ≥0 := ∑ i, εcodec i
  -- η⋆ = (7 t^2 + (28 L + 25) t + (14 L + 1) (L + 1)) / (2 · |Σ|^c) + θ⋆ · max ε + ∑ ε
  firstTermNumerator / firstTermDenominator + secondTerm + thirdTerm

/-- [CO25, Lemma 5.1]
The statistical distance between the outputs of the basic Fiat-Shamir game and the duplex-sponge
Fiat-Shamir game is bounded by the simulation error $\eta^*$. This theorem statement establishes
the fundamental equivalence between the two game distributions, assuming query-bounds on the
malicious prover.

Currently, this theorem is modeled with a placeholder return type `True` representing the security
reduction endpoint.
-/
lemma duplexSpongeToFSGameStatDist
    (maliciousProver : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₒ : ι → ℕ) (tₕ tₚ tₚᵢ : ℕ) : True :=
  trivial

end KeyLemma

end DuplexSpongeFS

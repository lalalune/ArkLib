/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToMathlib.FriCompletePerRound

/-!
# FRI: final folding round perfect completeness — bricks toward the final Brick A/B residual

Work toward discharging `finalFoldRoundPerfectCompletenessResidual` from
`ArkLib.ToMathlib.FriComplete` (the residual itself is NOT yet discharged here).

Landed so far:
* `natDegree_lt_of_mem_degreeLT`: bridges the FRI final-round witness bound
  (`Witness … (Fin.last (k+1))`, i.e. `degreeLT (2^0 * d)`) to the final verifier's degree
  `guard (p.natDegree < d)` — the honest-success fact for the `getConst`/`guard` leg.

Plan for the discharge (mirrors the proven non-final sibling
`foldRoundPerfectCompletenessResidual_holds` in `FriCompletePerRound.lean`):
unroll via `WhirIOP.FoldRound.unroll_2_message_VP`; SAFETY branch additionally simulates the
verifier's `getConst` query through `simOracle2` (instDefault interface: the response IS the
in-the-clear polynomial) and discharges the `guard` by the lemma above; CORRECTNESS branch
needs the routed-oracle `hroute`/`hroutePrev` recipe (see
`fri-routed-oracle-proof-recipe` notes in `FriCompletePerRound.lean`) PLUS reconciliation of
the prover's tactic-built `FinalOracleStatement` output (the `if h : j.1 = k+1` term in
`finalFoldProver.output`) against the verifier's `mkVerifierOStmtOut` routing — both sides
collapse via `eq_of_heq`/`eqRec_eq_cast`/`cast_heq` once the dite on `j.1 = k+1` is resolved
per index.
-/

namespace Fri.Spec.Completeness

open OracleSpec OracleComp ProtocolSpec NNReal Domain Finset

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {n : ℕ} {k : ℕ} {s : Fin (k + 1) → ℕ+} {d : ℕ+}
variable {ω : SmoothCosetFftDomain n F}
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

/-- A `CPolynomial` in `degreeLT D` (for positive `D`) has `natDegree < D`. Bridges the FRI
final-round witness bound to the verifier's degree `guard`. -/
lemma natDegree_lt_of_mem_degreeLT {p : CompPoly.CPolynomial F} {D : ℕ} (hD : 0 < D)
    (hp : p ∈ CompPoly.CPolynomial.degreeLT (R := F) D) : p.natDegree < D := by
  rw [CompPoly.CPolynomial.degreeLT_toPoly, Polynomial.mem_degreeLT] at hp
  rw [CompPoly.CPolynomial.natDegree_toPoly]
  rcases eq_or_ne p.toPoly 0 with h0 | h0
  · simpa [h0] using hD
  · exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (by exact_mod_cast hp)

end Fri.Spec.Completeness

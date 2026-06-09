/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.S5Genuine
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2MatchMonic

set_option linter.style.longLine false

/-!
# BCIKS20 §5.2.6–5.2.7 — Claims 5.8 / 5.8' UNCONDITIONAL for monic `H` (issue #232)

The §5 endpoints in `S5Genuine.lean` (`claim58_genuine`, `claim58prime_genuine`) prove the genuine
BCIKS20 X-degree bound on the Hensel root `γ = gammaGenuine`, but each carries the explicit
combinatorial Appendix-A.4 hypothesis `FaaDiBrunoSuccSumZeroResidual` (equivalently the lift-identity
bridge `LiftIdentityAt` / the carved `RestrictedFaaDiBrunoMatch`).

That residual is **PROVEN unconditionally for monic `H`** — `restrictedFaaDiBrunoMatch_of_monic`
(`P2MatchMonic.lean`) discharges the carved Faà-di-Bruno partition match from the genuine algebra
(`taylorCollapse`, `partitionProd_coeff_assembled`, the `W = 1` collapse), using `H.leadingCoeff = 1`
load-bearingly. This file simply **propagates that discharge up to the §5 Claims 5.8 / 5.8'**, so the
X-degree-bound conclusions hold with the residual hypothesis removed.

Why monic is the right (and only correct) form: the residual is **provably false for non-monic `H`**
— `P2OrderZeroRefutationWitness.βHenselAssembled_eq_gammaGenuine_false` exhibits a concrete
`H = 2·Y` over `ℚ` for which the `(A.1)` numerator series is mis-normalized (off by `W^{t+1}`
factors) and is NOT the genuine root. In the BCIKS20 setting `H` is an irreducible factor of the GS
interpolant over `F(Z)`, which is taken monic WLOG, so `H.leadingCoeff = 1` is exactly the genuine
hypothesis; making these claims unconditional under it is the faithful reading.

## What remains open (HONESTY)

This file closes the residual hypothesis at the §5 X-degree endpoints; it does **not** close the
top-level Johnson-regime MCA bound. The entire BCIKS20 Faà-di-Bruno / Hensel development is a
dependency island that the `Hab25*` algebraic-cover bridge does not yet import: the bridge
(`epsMCA_rs_le_johnsonBoundReal_of_algebraic_cover`) consumes a `Hab25JohnsonAlgebraicData` whose
exceptional-scalar cover is never constructed from the Hensel discharge. Wiring those together
(`Hab25JohnsonAlgebraicData.ofMonicHenselFactors`) plus Claim 5.9 (the Z-degree-1 structure) is the
remaining Johnson-regime formalization. None of this is the genuinely-open $1M capacity prize, which
is the field-universal beyond-Johnson core — separate from and beyond this known-math Johnson work.

## Main results (all axiom-clean, all unconditional under `H.leadingCoeff = 1`)

* `claim58_genuine_of_monic` — Claim 5.8: `αGenuine t = 0` from the §5 largeness alone (no residual).
* `claim58prime_genuine_tail_of_monic` — the `∀ t ≥ k` tail vanishing (no residual).
* `claim58prime_genuine_of_monic` — Claim 5.8': `γ = ↑(trunc k γ)` (`γ` is a polynomial), no residual.
* `gammaGenuine_isPoly_of_monic` — the packaged "`γ ∈ L[X]` of X-degree `< n+1`" existential form.
-/

noncomputable section

open scoped BigOperators
open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA
open ProximityPrize.BCIKS20.GammaGenuine

namespace BCIKS20.HenselNumerator.S5Genuine

variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

/-- **Claim 5.8 (genuine), unconditional for monic `H`.**
`αGenuine t = 0` from the §5 largeness hypothesis alone: the Appendix-A.4 residual is discharged by
`restrictedFaaDiBrunoMatch_of_monic`. Strictly stronger than `claim58_genuine_via_intree`, which also
requires `FaaDiBrunoSuccSumZeroResidual`. -/
theorem claim58_genuine_of_monic {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1)
    {t : ℕ} (hlarge : SβLargeAt H x₀ R hHyp t) :
    αGenuine H x₀ R hHyp t = 0 :=
  claim58_genuine_via_restrictedMatch H hHyp
    (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc) hlarge

/-- **Claim 5.8' tail vanishing (genuine), unconditional for monic `H`.**
Every coefficient `αGenuine t` with `t ≥ k` vanishes, given the `∀ t ≥ k` §5 largeness. -/
theorem claim58prime_genuine_tail_of_monic {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t) :
    ∀ t ≥ k, αGenuine H x₀ R hHyp t = 0 :=
  fun t ht => claim58_genuine_of_monic H hHyp hlc (hlarge t ht)

/-- **Claim 5.8' (genuine, polynomial form), unconditional for monic `H`.**
`γ = γ_k`: the genuine Hensel root `gammaGenuine` equals the coercion of its degree-`< k` truncation
polynomial. The "γ is a polynomial of X-degree `< k`" content with the A.4 residual removed. -/
theorem claim58prime_genuine_of_monic {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) {k : ℕ}
    (hlarge : ∀ t ≥ k, SβLargeAt H x₀ R hHyp t) :
    gammaGenuine x₀ R H hHyp
      = (↑(PowerSeries.trunc k (gammaGenuine x₀ R H hHyp)) : (𝕃 H)⟦X⟧) :=
  claim58prime_genuine_via_restrictedMatch H hHyp
    (restrictedFaaDiBrunoMatch_of_monic H x₀ R hHyp hlc) hlarge

/-- **BCIKS20 Claim 5.8' packaged (genuine), unconditional for monic `H`.**
The genuine Hensel root `γ = gammaGenuine` IS a polynomial in `(𝕃 H)[X]` of X-degree `< n+1`
(i.e. `≤ n`), given the §5 largeness for every `t ≥ n+1`. Combines the truncation equality
`claim58prime_genuine_of_monic` with the unconditional degree bound
`claim58prime_genuine_natDegree_lt`. This is the faithful machine-checkable form of
`γ = γ_k ∈ L[X]` (fulltext line 1695) with the Appendix-A.4 residual discharged. -/
theorem gammaGenuine_isPoly_of_monic {x₀ : F} {R : F[X][X][Y]}
    (hHyp : ClaimA2.Hypotheses x₀ R H) (hlc : H.leadingCoeff = 1) {n : ℕ}
    (hlarge : ∀ t ≥ n + 1, SβLargeAt H x₀ R hHyp t) :
    ∃ p : (𝕃 H)[X], p.natDegree < n + 1 ∧
      gammaGenuine x₀ R H hHyp = (↑p : (𝕃 H)⟦X⟧) :=
  ⟨PowerSeries.trunc (n + 1) (gammaGenuine x₀ R H hHyp),
    claim58prime_genuine_natDegree_lt H hHyp n,
    claim58prime_genuine_of_monic H hHyp hlc hlarge⟩

end BCIKS20.HenselNumerator.S5Genuine

section AxiomAudit
#print axioms BCIKS20.HenselNumerator.S5Genuine.claim58_genuine_of_monic
#print axioms BCIKS20.HenselNumerator.S5Genuine.claim58prime_genuine_tail_of_monic
#print axioms BCIKS20.HenselNumerator.S5Genuine.claim58prime_genuine_of_monic
#print axioms BCIKS20.HenselNumerator.S5Genuine.gammaGenuine_isPoly_of_monic
end AxiomAudit

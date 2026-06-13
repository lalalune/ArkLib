/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.KKH26CeilingMarch
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS
import ArkLib.Data.CodingTheory.ProximityGap.OwnershipCensusSharpened
import ArkLib.Data.CodingTheory.ProximityGap.GVHBKEnergyReduction
import ArkLib.Data.CodingTheory.ProximityGap.BoundarySupExactness
import ArkLib.Data.CodingTheory.ProximityGap.FarCosetExplosion
-- §2.3 live reduction dossier (#371 closed, #389 open):
import ArkLib.Data.CodingTheory.ProximityGap.CensusDominationWeld
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DeltaStarPinAllWitness
import ArkLib.Data.CodingTheory.ProximityGap.PinBeyondJohnson
import ArkLib.Data.CodingTheory.ProximityGap.PackingDeepBandMiss
import ArkLib.Data.CodingTheory.ProximityGap.UniversalBelowUDR
import ArkLib.Data.CodingTheory.ProximityGap.EsymmFiberCodewordList
import ArkLib.Data.CodingTheory.ProximityGap.MonomialSupplyChoose
-- §2.5 live routes (LD⇒MCA frontier):
import ArkLib.Data.CodingTheory.ProximityGap.GG25CurveDecodability
import ArkLib.Data.CodingTheory.ProximityGap.GG25MarkedCurve
import ArkLib.Data.CodingTheory.ProximityGap.CurveCloseSetTargetBound
import ArkLib.Data.CodingTheory.ProximityGap.FoldedCurveCloseSetBound
import ArkLib.Data.CodingTheory.ProximityGap.SeparationSurvivalCount
import ArkLib.Data.CodingTheory.ProximityGap.SubspaceDesignLineDecodable
-- §2.6 GM-MDS route:
import ArkLib.Data.CodingTheory.GMMDS.LovettThm17Reduction
import ArkLib.Data.CodingTheory.GMMDS.LovettLemma22
import ArkLib.Data.CodingTheory.GMMDS.LovettSeparateStep
import ArkLib.Data.CodingTheory.GMMDS.LovettDivisibility
-- §3 THE SHAW OPERATOR — the unified unknown + the closed prize conjecture:
import ArkLib.Data.CodingTheory.ProximityGap.ShawOperator
-- §Y the explicit entropy closed-form δ* value + the rigorous in-window ladder ceiling:
import ArkLib.Data.CodingTheory.ProximityGap.PrizeEntropyDeltaStar

/-!
# ╔══════════════════════════════════════════════════════════════════════════════╗
# ║   THE PROXIMITY PRIZE WORKBENCH  ·  one file, everything you need, write here  ║
# ╚══════════════════════════════════════════════════════════════════════════════╝

**Mission (proximityprize.org / ABF26 = Arnon–Boneh–Fenzi 2026, ePrint 2026/680).**
Produce a *novel, complete, closed* conjecture (no further open math, no incomputable lemma)
that **simultaneously resolves both grand challenges** for *explicit, constant-rate, smooth*
Reed–Solomon codes in the **prize regime** — and prove it. The two challenges are the same
δ* up to the LD⇒MCA bridge; the genuine open core is ONE object (§3).

────────────────────────────────────────────────────────────────────────────────
## §0.  THE PRIZE REGIME — pin this or you are wasting time
────────────────────────────────────────────────────────────────────────────────
* Code: `C = RS[F, L, k]`, `L` a **smooth** (FFT/NTT, multiplicative-subgroup `μ_n`)
  evaluation domain, `n = |L| = Fintype.card ι`.
* Rate: `ρ = k/n ∈ {1/2, 1/4, 1/8, 1/16}` — **constant rate**, so `k = Θ(n)` (`prizeRates`).
* Threshold: `ε* = 2^(-128)` (`epsStar`); operationally `q·ε* ≈ n` for `q ≈ n·2^128`.
* Field: `q = |F|` large, `q ≈ n·2^128` (so `q·ε* ≈ n`); positive rate `0 < k`.
* Target window: pin `δ*` in the **window interior** `(1−√ρ, 1−ρ−Θ(1/log n))` — the
  beyond-Johnson, below-capacity band. Johnson `1−√ρ` is already done; capacity `1−ρ` is
  the wall. **Anything that reduces to Johnson, to capacity-for-constant-DIM, or to an
  incomputable lemma is OUT.**

⚠️ **DEGENERACY TRAP (do not target these).** The *real-valued* `grandMCAChallenge` /
`grandListDecodingChallenge` collapse: `grandMCAChallenge_iff_epsMCA_one` (radius-one only),
and `not_grandListDecodingChallengeRS_of_pos` (the LD one is *false* for `0<k`, `ε*<1`).
**The faithful targets are `mcaConjecture` (§1) and the operational `mcaDeltaStar` (§2).**

────────────────────────────────────────────────────────────────────────────────
## §1.  THE EXACT TARGET  (prove ONE of these — they are the prize)
────────────────────────────────────────────────────────────────────────────────
**(T1) The uniform MCA conjecture** `ProximityGap.mcaConjecture` (ABF26 §4.5):
  `∃ c₁ c₂ c₃, ∀ RS[F,L,k], ∀ δ < 1−ρ,  ε_mca(RS,δ) ≤ (1/q)·n^{c₁}/(ρ^{c₂}·η^{c₃})`,
  `η = 1−ρ−δ`. Constants quantified BEFORE the ∀-over-codes. Proving this resolves the
  MCA prize at every rate (`nonempty_mcaLowerWitness_of_mcaConjecture` → `mcaPrize`).
**(T2) A `GrandMCAResolution`** for each prize rate: a maximal `δ*` with `ε_mca(C,δ*)≤ε*`
  and strict failure above. Equivalent to pinning the operational `mcaDeltaStar` (§2).
**(T3) Either ⟹ the LD prize** via the LD⇒MCA bridge (`GG25MCAFromCurveDecodability`,
  the §3.x curve-decodability route) — the two challenges share `δ*`.

The `YOUR CONJECTURE HERE` slot at the bottom is where the closed-form `δ*(ρ,ε*,n)` and its
proof go. It must be **complete**: a single computable `δ*`-expression, proven, no residual.

────────────────────────────────────────────────────────────────────────────────
## §2.  THE SUBSTRATE  (PROVEN, axiom-clean, ready to apply — build on these)
────────────────────────────────────────────────────────────────────────────────
**The governing law** (`MCAThresholdLedger`):
  `mcaDeltaStar C ε* = sup{δ : max-far-line-incidence(δ) ≤ q·ε*}`.
  · `le_mcaDeltaStar_of_good`  — lower bound on δ* from a good radius (incidence ≤ q·ε*).
  · `mcaDeltaStar_le_of_bad`   — upper bound on δ* from a bad witness.
  · `FarCosetExplosion.epsMCA_ge_far_incidence` — `ε_mca ≥ incidence/q` (the law's engine).

**Capacity side — SOLVED for constant DIMENSION `k=O(1)`** (NOT the prize, but the template):
  · `KKH26CeilingMarch.interiorCeiling_march` — worst-case `incidence(1−r/2^μ) ≤ C(n,r)/r`
    (iSup over ALL stacks), ⟹ FFT-domain RS reaches `δ*=(1−ρ)−1/n` for `k=O(1)`.
  · `KKH26CeilingMarch.march_badScalars_card_mul_le` — `#bad·(d+2) ≤ C(n,d+2)` (the count).

**Granularity ladder** (`GranularityLadderRS.mcaDeltaStar_rs_eq_granularity`):
  `δ* = j/n` on bands `3(j−1)+k ≤ n`, `j+1+k ≤ n`, `j+1 ≤ q`, `ε*∈[j/q,(j+1)/q)`. EXACT.

**Boundary law** (`BoundarySupExactness.rs_boundary_epsMCA_eq`):
  `ε_mca(RS, δ) = n/q` for `3∣n`, `6<n`, `k=n−4`, `2 ≤ δ·n < 3`.

**Ownership count — PROVEN TIGHTLY BRACKETED** (`OwnershipCensusSharpened`):
  · `sharpened_badScalars_card_mul_choose_le` — `#bad·C(w₀+1,d+1) ≤ C(n,d+1)·(n−d−1)` (LOWER).
  · `deviation_ownership_card` — the CEILING: deviation stacks realize EXACTLY `C(w−1,d+1)`,
    so NO per-witness-subset bound can do better. **This surface is PROVEN EXHAUSTED (§3).**
  · `sharpened_epsMCA_le` — wires the sharpened count to `epsMCA`.

**Energy / sub-Johnson list chain** (`GVHBKEnergyReduction`, `AdditiveEnergyRepBound`):
  `GVRepBound G M` (`r(c)≤4|G|^{2/3}`) ⟹ `E(G)³ ≤ 260|G|⁸` ⟹ list `T ≲ n^{11/6} ≪ n²`.
  **√-loss is FATAL** (`T² ≤ |G|·E`; even `E=|G|²` → list `n^{3/2}`, sub-Johnson not capacity).

**Paper-bound bridges** (`GrandChallenges`, all wired to witnesses):
  GKL24 `MCALowerWitness.ofLinearOnePointFiveJohnsonGKL24`, BCHKS25 `…ofJohnsonBCHKS25` /
  `…ofJohnsonJumpBCHKS25AutoRadius`, CS25 `…ofRSBreakdownCS25` (capacity-side ε_ca=1),
  KK25 `…ofLowerCapacityBCHKS25KK25`, DG25 `…ofSamplingDG25`.

────────────────────────────────────────────────────────────────────────────────
## §2.5  LIVE ATTACK ROUTES  (freshest in-progress machinery — the actual frontier)
────────────────────────────────────────────────────────────────────────────────
Three routes from the latest literature connect the LD challenge to the MCA challenge (solve
one ⟹ solve both). Each is mostly built in-tree; its GAP is the one open piece to attack.

**(R1) GG25 curve-decodability ⟹ MCA** (Guruswami–Gabizon, ePrint 2025/2054).
  · `ProximityGap.CurveDecodable C ℓ δ a b` / `MarkedCurveDecodable` — a degree-`ℓ` curve
    through `a` close points explains `≥ b` of them. (`GG25CurveDecodability`, `GG25MarkedCurve`.)
  · `GG25Lemma32.disagree_spread_bound` (Lemma 3.2) + `GG25MCAFromCurveDecodability`
    (`all_seeds_relClose`) — **curve-decodability ⟹ MCA (Thm 3.3), DONE** modulo the input.
  · **GAP:** GG25 proves curve-decodability only for FRS / multiplicity / random RS (field
    LINEAR in `n`), NOT explicit plain RS (the prize). Plain-RS curve-decodability is open.

**(R2) CZ25 subspace-design list-recovery** (the GG25 §4.3 curve-decodability argument).
  · `ProximityGap.exists_determining_tuple` — a tuple `v ⊆ T` whose coordinates **determine**
    a dim-`≤ r` list span `H`, when design param `θ < θ' = 1−δ`. Axiom-clean (`SubspaceDesignLineDecodable`).
  · `SeparationSurvivalCount.card_surv_ge` — combined separation + agreement count.
  · **GAP:** needs the list-recovery input `CZ25CoordFiberCap` (the `δ`-close codewords span dim `≤ r`).

**(R3) GM-MDS / Lovett higher-order MDS ⟸ δ*** (Lovett arXiv:1803.02523, AGL24).
  · `ArkLib/Data/CodingTheory/GMMDS/Lovett*` (10+ files) — the chain `δ* ⟸ L(δ) ⟸ higher-order
    MDS` reduces to the last residual `AGL24.GMMDSDualZeroPatternTheorem` (dual zero pattern).
  · **GAP:** the dual-zero-pattern theorem.

**(R4) The SYMMETRIC-FUNCTION / coset-rigidity route — the direct far-line incidence, reduced.**
  The far-line incidence is `Z/n`-dilation-invariant, so the extremal directions are monomials
  `X^a` (`FarLineIncidenceEquivariance`); the subgroup directions `X^{n/2}` are CORRELATED and
  discarded (`MonomialSubgroupCorrelated.lean`: `X^{n/2}=±1` on `μ_n`; jointly close on `μ_{n/2}`).
  For a NON-correlated direction `(X^a, X^b)`, working `mod m_S = ∏_{x∈S}(X−x)` (`S` the agreement
  set, `|S| = w = (1−δ)n`) the residues `X^{w−1+j} mod m_S` have complete-homogeneous-symmetric
  coefficients, so the bad scalar is a fixed symmetric function `γ = σ(e_•(S))` under vanishing
  of further symmetric functions of `S`. CLEANEST case `dir(k+1,k+2)`, `w=k+2` (PROVEN reduction,
  `probe_symmetric_function_reduction.py`, verified vs exact list-decode):
    `B = { −e_1(S) : S ⊆ μ_n, |S| = k+2, e_2(S) = 0 }`.
  · **MEASURED (the prize-regime facts):** the worst non-correlated incidence is **q-INDEPENDENT**
    and **`O(n)`** (`dir(5,7)`: `64,72,40,40` over `q=97..353`; `dir(5,6)→n`), crossing the prize
    level `q·ε* = n` strictly **inside the window** `(1−√ρ, 1−ρ)` (between `δ=0.562` and `0.625`
    at `n=16,ρ=1/4`). The bad set is a union of `μ_{n'}` cosets (`n'=n/gcd(b−a,n)`).
  · **GAP (the conjecture to prove — beats W4):** the symmetric-function value set
    `{ σ(S) : S ⊆ μ_n, |S|=w, vanishing-symmetric constraints }` has **`O(1)` `μ_n`-cosets**, i.e.
    worst non-correlated incidence `≤ C·n`. This is a CONCRETE, **q-independent** cyclotomic
    symmetric-function statement — it does NOT route through the incomplete-Gauss-sum-over-`F_q`
    wall (W4); the `q`-independence (proven by `mca_badscalar_general`, `#bad ≤ C(n,w)`) makes the
    whole quantity finite combinatorial. Proving the `O(n)` coset bound + the incidence/`δ*`
    calibration (worst incidence `= n` at `δ = δ*`) closes the MCA prize directly. The dilation
    `γ_S ↦ g^{b−a}γ_S` forces the coset structure; the open content is the *rigidity* (why all
    consistent `S` collapse to `O(1)` cosets).

Each GAP is a candidate `YOUR CONJECTURE HERE`: a closed plain-RS curve-decodability bound (R1),
a closed `CZ25CoordFiberCap` list-recovery dim bound (R2), the dual-zero-pattern theorem (R3),
or the `O(n)` symmetric-function coset-rigidity bound (R4) — any one, proved in the prize regime
without residual, closes the prize via its bridge.

────────────────────────────────────────────────────────────────────────────────
## §3.  THE WALLS  (PROVEN dead ends — every accessible technique stops here)
────────────────────────────────────────────────────────────────────────────────
**(W1) Per-witness counting is PROVEN EXHAUSTED.** `deviation_ownership_card` caps ownership
  at `C(w−1,d+1)`; production `k=Θ(ρn)` (`r=Θ(n)`) needs ownership `e^{Θ(n)}` while the
  scheme caps at `r+1`. The δ* prize needs *a genuinely different counting surface* — none known.
**(W2) Energy is the wrong lever.** Open at exponent `2+o(1)` (hard `7/3` barrier); above
  `p^{2/3}` no nontrivial subgroup-energy bound exists; and the √-loss (W-chain above) caps
  any energy bound at sub-Johnson. `WeilRegimeClosure` "capacity" = LARP (supply ≠ incidence).
**(W3) Confluent-Stepanov `n^{2/3}`** (the energy route's sharp input) needs the `a`-mixing
  Wronskian rep-point multiplicity — explicit caps at order 2, moment-combination trivial,
  same-`a`/distinct-roots/2-relation all fail (5 angles). Multi-week, no separable entry brick.
**(W4) Weil/√q wall.** `|η_b| ≪ √q` is vacuous for `|G|<√q`; coordinate-pigeonhole incidence
  surface refuted (target is the low-weight-error syndrome *variety*, not a coordinate ball).
**(W5) The budget/supply route pins δ* but ONLY ABOVE the window — PROVEN.** The all-stack
  `allWitnessDom_epsMCA_le` (`iSup` over *every* word stack — a *different* counting surface than
  W1's per-witness one) composed with the KKH26 upper witness PINS `δ* = 1−r/2^μ`
  UNCONDITIONALLY for the bulk/low-degree range, no `CensusDomination`
  (`KKH26AllWitnessPin.kkh26_deltaStar_pin_allWitness`; the budget-below-supply arithmetic is
  discharged outright for all `r ≤ √(2^μ)` by `choose_bulk`, giving the infinite family
  `kkh26_deltaStar_pin_lowdegree`; concrete `δ*=3/4` at `kkh26_deltaStar_pin_allWitness`'s
  `deltaStar_pin_concrete_F4129`; all axiom-clean). BUT this pins `δ*` at `ε* = supply/p`, and
  `1−r/2^μ = 1−ρ−Θ(2^{−μ})` sits in the near-capacity strip `(1−ρ−Θ(1/log n), 1−ρ)` — STRICTLY
  ABOVE the window-upper `1−ρ−Θ(1/log n)` for *every* `(μ,r)` (verified `in-win? = False`,
  `scripts/probes/probe_deltastar_window_calibration.py`). So the budget/supply machinery, though
  unconditional and general, structurally CANNOT reach the window interior: the prize `ε*=2^{−128}`
  is a *different, smaller* point on the `δ*(ε*)` curve where the line–ball incidence must be
  *sub-exponential* (= the open W4 incidence / incomplete-Gauss-sum problem). Do not expect a
  sharper budget/supply count to win the prize — it provably pins the wrong point.
**(W6) The second-moment / Fourier-L² method is PROVEN EXHAUSTED (machine-checked, `ShawSecondMoment`).**
  The Shaw operator's exact second moment `∑_{s₀}‖𝒮‖² = |V|·M`, `M = ∑_{ψ≠0,ψ⊥s₁}‖Ŝ(ψ)‖²`
  (`shawError_second_moment`) brackets the prize's worst case
  `max_{s₀}‖𝒮‖ ∈ [√M, √(|V|·M)]` (`exists_shawError_sq_ge` + `shawError_sq_le_second_moment`) — a
  multiplicative gap of EXACTLY `√|V| = q^{n/2}` (the union tax over the `|V|` base points). So no
  L²/moment/union argument can *certify* `‖𝒮‖≤B`; it can only *falsify*
  (`not_mcaShawConjecture_of_lt_secondMoment`: `B²<M ⟹` the bound fails — an unconditional δ* CEILING).
  The far-coset restriction is FORCED, not a convention: a fully-contained line gives `𝒮 = |V|−|S|`
  exactly (`shawError_of_line_subset`, `not_mcaShawConjecture_of_line_subset`). **REGIME TRAP (avoided):**
  the single-Hamming-ball model makes the prize trivial (`incidence ≤ ⌊w₁/(w₁−R)⌋ < budget`); the TRUE
  object is `S = δ-neighborhood of the CODE C`, so `M = ∑_{ψ∈C^⊥, ψ⊥s₁, ψ≠0} |K(wt ψ)|²` — the
  **dual-code Krawtchouk sum**, whose uniform worst-`u₀` bound IS W4 (and equals the list-size bound, so
  one bound closes BOTH challenges). The prize needs genuine uniform √-cancellation of THAT sum, beyond
  any L² estimate.

────────────────────────────────────────────────────────────────────────────────
## §4.  WHAT A WINNING CONJECTURE MUST DO  (the closure contract)
────────────────────────────────────────────────────────────────────────────────
1. Give a **single computable** `δ*(ρ, ε*, n)` (or an `ε_mca(RS,δ)` bound) — no `∃`-over-
   incomputable objects, no named residual, no further open lemma.
2. Hold in the **prize regime** (constant `ρ`, `k=Θ(n)`, `q≈n·2^128`) — verify it does NOT
   collapse to Johnson (`1−√ρ`) or to the constant-DIM capacity result (`interiorCeiling_march`).
3. Beat the per-witness wall (W1): the incidence bound must NOT route through per-witness
   subset ownership (proven `e^{Θ(n)}`-short). It needs a new counting surface.
4. Be **machine-checkable**: instantiate at one concrete prize-shaped RS code and `decide`/
   prove the bound, then prove the general statement.

Once proved, wire it to `mcaConjecture` (T1) or a `GrandMCAResolution` (T2), then to the LD
prize via the GG25 curve-decodability bridge (T3).

────────────────────────────────────────────────────────────────────────────────
## §R.  RESEARCH SYNTHESIS 2026-06-13 — the two challenges collapse to ONE δ*, and
##      every published route provably misses the prize regime (plain RS, s=1).
##      (full map: `docs/kb/jlr26-frs-subspace-design-formalization-map-2026-06-13.md`)
────────────────────────────────────────────────────────────────────────────────
**THE REDUCTION (defensible, from the ABF26 bridges).** The grand MCA challenge and the grand
list-decoding challenge share the *same* `δ*`:
  · MCA ⟹ list  (ABF26 Thm 5.2 [BCHKS25 1.9] / Thm 5.3 [CS25 2]): `ε_mca ≤ ε*` ⟹ `|Λ| ≲ ε*·|F|`.
  · list ⟹ MCA  (ABF26 Thm 5.1 [GCXK25 3]): `|Λ(C,δ)| ≤ L` ⟹ `ε_mca(C, 1−√(1−δ+η)) ≤ L²δn/(η|F|)`.
With `ε*=2⁻¹²⁸`, `q≈n·2¹²⁸`, so `ε*·|F| ≈ n`, hence the prize core is exactly:

  **`δ*_prize = sup{ δ : |Λ(RS[F, μ_n, k], δ)| ≤ ε*·|F| ≈ n }`**  — the radius where the
  *worst-case list size of explicit smooth-domain RS* crosses `~n`. Pin THIS and both fall.

**THE THREE PUBLISHED ROUTES AND THEIR FATAL GAPS (exhaustive — none reaches plain RS, s=1):**
  1. **List⇒CA** (GCXK25 Thm 3): has a **√-loss in the radius** (`δ → 1−√(1−δ)`) that ABF26 proves
     is FALSE to remove in general (Thm 5.4 [BGKS20] counterexample). OUT unless smooth structure.
  2. **Subspace-design / line-stitching** (JLR26 = arXiv 2601.10047 / GG25 = 2025/2054): proves
     `ε_mca ≤ (C₁/q)(n/η+1/η³)` up to capacity δ=1−R−η, BUT is **FRS-only** — needs folding
     `m=Ω(η⁻²)`; plain RS (`s=1`) has `τ(r)=R+O(r)`, useless. Its lemma chain is ~70% in-tree:
     Claim 5.8 = `subspaceDesign_list_dim_bound`, Lemma 5.4 = `curve_agreement_card_le` (both
     landed), Def 4.3 = `IsSubspaceDesign`, Lemma 5.5 = `exists_separating_*` (fleet); only line
     stitching (5.7) + peeling (5.10) remain — relevant for the FRS arm, NOT the prize.
  3. **Syndrome-space + witness reduction** (Yuan–Zhu arXiv 2605.07595, May 2026): `ρ<1−R−ε`
     up to capacity WITHOUT list decoding — but **random linear codes only** (random parity-check
     model); it works precisely because the random syndrome avoids `μ_n`'s additive structure.

**THE SINGLE NAMED OPEN TARGET (the prize core, no open-ended search).** Transferring route 3 to
explicit `μ_n` is the **line–ball incidence in syndrome space** (face iv, `epsMCA_ge_far_incidence`):
the bad-scalar count is `max over far-direction lines |{γ : syn(u₀)+γ·syn(u₁) ∈ B_{⌊δn⌋}}|`, where
`B_w` is the weight-`w` syndrome ball = high-frequency DFT image of weight-`≤w` errors over `μ_n`.
Pinning `δ*` is bounding this incidence; the controlling quantity is the **additive-energy / Sidon
structure of `μ_n`** (the in-tree energy + this-session antipodal work). A winning closed conjecture
states `max-incidence(δ) ≤ f(n,ρ,δ)` in closed form, with `f` crossing `n` at the claimed `δ*`, and
respecting the near-capacity lower bound `ε_mca ≥ n^{Ω(1)}/|F|` (ABF26 Table 1). This is the
`▼ YOUR CONJECTURE HERE ▼` slot's precise target — a syndrome line–ball incidence bound for `μ_n`.

## §R.2  SESSION 2026-06-13b — energy⟹sup-norm reduction, the EXACT constant √2, and the proven
##        BGK partial bound (connecting the Shaw operator of §3 to known number theory).

The §3 Shaw operator's even moments ARE the `r`-fold additive energies `E_r(μ_n)` of the syndrome
incidence, so the prize bound is a bound on `E_r(μ_n)`. Three results this session:

  **(1) Reduction, LANDED axiom-clean** (`SubgroupGaussSumEnergyReduction.eta_pow_le_energyR`):
  `max_{b≠0}‖η_b‖^{2r} ≤ q·E_r(μ_n) − |μ_n|^{2r}`, via the in-tree moment ladder
  `∑_b‖η_b‖^{2r}=q·E_r` (pure orthogonality, no Weil). Converts ANY `E_r` bound into a Shaw/η bound.

  **(2) The EXACT prize constant √2** (char-0 Wick). For `n=2^μ`, `{ζ^0..ζ^{n/2−1}}` is a ℚ-basis of
  `ℚ(ζ_n)`, so the char-0 `r`-fold energy is a pure matching count `E_r^ℂ(μ_n)=(2r−1)!!·n^r`
  (μ_n ≈ complex Gaussian; r=1→n, r=2→3n²−3n in-tree-exact). At the critical `r≈ln q` this yields
  `max‖η_b‖ ≤ √(2·n·ln q)`. The controlled quantity is the EXCESS over the equidistribution baseline,
  `Excess(r):=E_r−n^{2r}/q=(1/q)∑_{b≠0}‖η_b‖^{2r}`; the prize ⟺ `Excess(ln q) ≤ (2r−1)!!·n^r`. The
  `r=2` case is PROVEN in-tree (pinned `E_2=3n²−3n`, `n⁴/q≈2⁻⁹⁶` negligible) but gives only a trivial
  sup bound — the √2 needs `r≈ln q`, the open regime.

  **(3) Proven PARTIAL bound (BGK).** The prize needs only ENOUGH cancellation, not the sharp √2:
  the sharp sup-norm needs equidistribution to relative precision `e^{−Θ(n)}` (absurd) and was an
  over-strong side-target. Throughout the ENTIRE prize regime `n=2⁴⁰ ≥ p^{0.156}` (fixed `δ` since
  `p≤2²⁵⁶`), Bourgain–Glibichuk–Konyagin gives a PROVEN power-saving `max‖η_b‖ ≤ n^{1−ε}`,
  `ε=ε(0.156)>0`. Via the in-tree `SubgroupGaussSumMomentBound.rEnergy_le` (with `M=n^{2−2ε}`) this is
  a proven `Excess(r) ≤ n^{2r−1−2ε(r−1)}` — strictly past Johnson, but `≫ Wick` for small `ε`, so it
  does NOT reach the window edge `1−ρ−Θ(1/log n)`.

So the prize is bracketed by two in-tree-expressible bounds on the SAME Shaw/`E_r` object: BGK
(proven, past Johnson) below, Wick-√2 (conjectured, window edge) above. The open core is exactly the
sharp per-frequency `Z/n` block estimate of `FarLineIncidenceEquivariance` (§3) — sharper than BGK,
= `Excess(ln q) ≤ (2r−1)!!n^r`. Full derivation + numerics:
`docs/kb/jlr26-frs-subspace-design-formalization-map-2026-06-13.md` §§13–14b.

## §R.3  SESSION 2026-06-13c — the IRREFUTABLE closed bound (fabricate-then-refute).

Filling the §R.2 bracket [BGK proven, below | sharp open, above] with a refutation-tested closed
form for the §3 Shaw-operator magnitude `S(n,p) = max_{b≠0}|∑_{x∈μ_n} e_p(bx)|`:

  **`S(n,p) ≤ 2·√(n · ln p)`   (uniform);   `S(n,p) = (1+o(1))·√(n ln p)`  (sharp law).**

Refutation ladder (FFT-exact, 2197 (n,p) pairs, n≤512, p≤250k, adversarial Fermat/2-power-heavy
primes + depth sweep): `C=1` REFUTED, `C=√2` (the char-0 Wick value of §R.2/§14) REFUTED,
`C=√e=1.6487` survives (sup 1.6378), `C=2` IRREFUTABLE (0/1690 violations). The char-p anomaly that
§R.2 left open is now valued: a BOUNDED Gumbel tail `max|η_b|²≈n(ln p+G)`, `G` peaking (≈19) at the
Fermat prime 65537 and NOT growing with `n` or 2-adic depth — so the constant is universal, between
`√2` (char-0) and `√e` (with anomalies). Mechanism: `η_b=(1/m)∑_{ψ∈μ_n^⊥,ψ≠1}ψ̄(b)τ(ψ)`,
`|τ(ψ)|=√p`, extreme value of `p` Gauss-phase terms.

**Closes both challenges (modulo proof of the bound).** Bias `θ=S/n ≤ 2√(ln p/n) → 0`; at the prize
point `n=2⁴⁰, p≤2²⁵⁶`, `θ ≤ 2^{-15}`. A `θ`-pseudorandom smooth RS code keeps list size `≤2^128`
through the window, so `δ* = 1−ρ−Θ(1/log n)` (ABF26 Thm 4.16 met). Via §3
`incidence_pinned_of_shawBound`, the closed bound `S ≤ 2√(n ln p)` IS the resolution: set the §3
`MCAShawConjecture` budget `B := 2√(n ln p)`. The remaining (tractable) proof target is a Gumbel-tail
bound on `∑_ψ ψ̄(b)τ(ψ)` (Deligne equidistribution + union bound over `b`) — replacing the FALSE
sharp-`√2` route. Refutation-tested CONJECTURE (n≤512 verified; n=2⁴⁰ is inductive extrapolation),
not a proof. Full record: `docs/kb/jlr26-frs-subspace-design-formalization-map-2026-06-13.md` §15.

## §R.4  SYNTHESIS 2026-06-13d — δ* is the CAPACITY term (Incidence-Genericity Dichotomy + refutation).

CORRECTION to the §R.3/window-edge reading, synthesizing the issue thread's Incidence-Genericity
Dichotomy with the fabricate-then-refute certificate.

  **`δ*(dyadic μ_{2^μ}, ε*) = H_q⁻¹(1 − ρ − log_q(1/ε*)/n)`**  (the list-decoding CAPACITY radius;
  ≈ `1 − ρ − h(1−ρ)/log₂q` to first order).

WHY (not the window edge): the KK25/BCHKS bad construction `δ*≤1−ρ−Θ(1/log n)` (Thm 4.16) is the
worst case over ALL domains — its construction is F₂-linear/special-sumset. The GENERIC dyadic
prime-field `μ_n` BEATS it and reaches the capacity term, because it is incidence-generic:
  · `B(μ_n) = max_{b≠0}|∑_{x∈μ_n}e_p(bx)| ≤ 2√(n ln p)` (refutation, §R.3) and
    `B(μ_n)/B_random ≈ 0.48–0.64 ≤ 1` — μ_n is at most as additively concentrated as a RANDOM
    n-subset (whose worst sum is also `√(n ln p)`);
  · `E(μ_n) = 3n²−3n` exactly (in-tree `RootsOfUnityEnergyExact`) = the CLEAN generic value
    (`E⁺/3n(n−1)=1`), the antipodal `−1∈μ_n` accounted for, NOT an inflation.

So both grand challenges share `δ* = ` the capacity radius. Open core (gated): deployed-regime
genericity `E(μ_n)=O(n²) ⟺ B(μ_n)=O(√(n·polylog))` (the 25-yr wall) — PROVEN for `p>2^n`
(cyclotomic resultant, in-tree), refutation-certified for deployed `p≈2^168≪2^{2^40}`, BGK-floored
`B≤n^{1−ε}`. The two remaining open links: the dichotomy's forward direction (generic ⟹ capacity δ*)
and the asymptotic genericity proof. Issue #389 comment 4699815321; KB §19.
-/

set_option linter.unusedSectionVars false
-- the prize objects (mcaDeltaStar, choose-budget) are heavy to elaborate; give a solver room:
set_option maxHeartbeats 1000000

namespace ProximityGap.Workbench

open scoped NNReal ENNReal
open ProximityGap ProximityGap.GrandChallenges
open ArkLib.ProximityGap.KKH26  -- evalCode: the explicit smooth RS code object used by the §2.4 pins
-- Substrate namespaces — every §2 lemma is now directly accessible by its short name:
open ProximityGap.MCAThresholdLedger      -- mcaDeltaStar, le_mcaDeltaStar_of_good, mcaDeltaStar_le_of_bad
open ProximityGap.FarCosetExplosion       -- epsMCA_ge_far_incidence (the law's engine)
open ProximityGap.SpikeFloor              -- mcaDeltaStar_rs_eq_granularity (the ladder)
open ArkLib.ProximityGap.KKH26CeilingMarch          -- interiorCeiling_march, march_badScalars_card_mul_le
open ArkLib.ProximityGap.OwnershipCensus            -- sharpened_*, deviation_ownership_card (the CEILING)
open ArkLib.ProximityGap.AdditiveEnergyRepBound     -- GVRepBound, additiveEnergy_cube_le_of_gvRepBound
open ProximityGap.BoundarySupExactness    -- rs_boundary_epsMCA_eq (the boundary n/q law)

/-! ## SMOKE TEST — every §2 substrate lemma resolves here (the "good experience" check).
If any `#check` below errors, the workbench is missing an import/open and must be fixed before
a solver relies on it. -/

-- §1 targets
#check @mcaConjecture
#check @GrandChallenges.mcaPrize
#check @GrandChallenges.mcaConjectureBound
#check @GrandChallenges.nonempty_mcaLowerWitness_of_mcaConjecture   -- conjecture ⟹ prize witness
-- §2 the law
#check @mcaDeltaStar
#check @le_mcaDeltaStar_of_good
#check @mcaDeltaStar_le_of_bad
#check @epsMCA_ge_far_incidence
-- §2 capacity-for-constant-DIM (the template, not the prize)
#check @interiorCeiling_march
#check @march_badScalars_card_mul_le
-- §2 granularity + boundary exact laws
#check @mcaDeltaStar_rs_eq_granularity
#check @rs_boundary_epsMCA_eq
-- §2 ownership bracket (W1: the proven-exhausted surface)
#check @sharpened_badScalars_card_mul_choose_le
#check @deviation_ownership_card
-- §2 energy / sub-Johnson list chain (W2/W3: the √-loss-capped route)
#check @additiveEnergy_cube_le_of_gvRepBound
-- §2 paper-bound witness bridges
#check @MCALowerWitness.ofJohnsonBCHKS25
#check @MCAUpperWitness.ofRSBreakdownCS25
-- §2.5 live LD⇒MCA routes (the frontier)
#check @CurveDecodable
#check @MarkedCurveDecodable
#check @exists_determining_tuple

/-! ## Sanity handles — the target objects are in scope and usable.

These trivial `example`s confirm the prize objects elaborate here, so a solver can write the
real statement directly against them. (They are not the prize; they certify the workbench.) -/

/-- The uniform MCA conjecture is the named target `Prop`. -/
example : Prop := mcaConjecture

/-- The MCA prize (all four rates, `ε* = 2^-128`) is in scope for any smooth domain. -/
example {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] (domain : ι ↪ F) : Prop :=
  GrandChallenges.mcaPrize domain

/-- The operational threshold `mcaDeltaStar` is in scope (the law's δ*). -/
noncomputable example {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}
    (C : Set (Fin n → F)) (εstar : ℝ≥0∞) : ℝ≥0 :=
  MCAThresholdLedger.mcaDeltaStar (F := F) (A := F) C εstar

/-! ════════════════════════════════════════════════════════════════════════════
    ║                     ▼▼▼   YOUR CONJECTURE HERE   ▼▼▼                       ║
    ════════════════════════════════════════════════════════════════════════════

    State the closed-form `δ*(ρ, ε*, n)` (or the `ε_mca` bound), prove it in the
    prize regime, beat the per-witness wall (W1), and wire it to `mcaConjecture`
    (T1) / a `GrandMCAResolution` (T2) / the LD prize (T3). Keep it CLOSED — no
    residual, no incomputable lemma. Prove a concrete prize-shaped instance first,
    then the general statement.

    Example skeletons (uncomment, replace `sorry` — but the prize needs NO sorry):

      -- def prizeDeltaStar (ρ : ℝ≥0) (n : ℕ) : ℝ≥0 := …            -- the closed form
      -- theorem prize_mcaConjecture : mcaConjecture := …            -- T1
      -- def prizeResolution … : GrandMCAResolution C epsStar := …   -- T2

    ════════════════════════════════════════════════════════════════════════════ -/

/-! ════════════════════════════════════════════════════════════════════════════
    ║   §3   THE SHAW OPERATOR — the closed Proximity-Prize conjecture           ║
    ════════════════════════════════════════════════════════════════════════════

    UNIFICATION (proven, axiom-clean, `ProximityGap.ShawOperator`).  Every reduction of the prize
    δ* — the residual `(R) = worst − average`, the higher-order-MDS failure-correction `κ_d`, the
    off-diagonal spectral error of the line–ball incidence operator, the worst-case incomplete
    character sum `max|η_b|`, the higher additive energies `E_r` — is **one** quantity, the

        **Shaw operator**   `𝒮(S; s₀, s₁) = Σ_{ψ≠0, ψ⊥s₁} Σ_{s∈S} ψ(s₀−s)`

    (`ShawOperator.shawError`), the off-trivial spectral error of the line–ball incidence.

    SOLVE FOR δ* (proven, axiom-clean).  `ShawOperator.incidence_eq_average_add_shaw`:

        `#{γ : s₀+γ·s₁ ∈ S} · |V|  =  |F| · (|S| + 𝒮)`     — incidence = average + Shaw, EXACTLY.

    Since `δ* = sup{δ : max-far-line-incidence(δ) ≤ q·ε*}` (`MCAThresholdLedger.mcaDeltaStar`), δ*
    is a *closed function* of the worst-case Shaw operator.  `incidence_pinned_of_shawBound` turns a
    Shaw budget into two-sided control of the incidence with **no open residual**.

    THE CLOSED CONJECTURE (the single open input).  `ShawOperator.MCAShawConjecture S B`:

        `∀ s₀ s₁,  ‖𝒮(S; s₀, s₁)‖ ≤ B`.

    With the prize budget `B = q·ε*·|V|/|F| − |S|` on the explicit smooth-domain δ-ball this is
    EXACTLY δ* reaching the prize window.  It is irreducible: NOT Johnson (the average term is
    strictly capacity-side), NOT a Weil/Parseval bound (W4-weak on `s₁^⊥` for `n ≪ √q`).  This is a
    closed bound on a single named operator — no residual, no incomputable lemma.  Proving it (the
    cyclic block-diagonal `Z/n` per-frequency estimate of `FarLineIncidenceEquivariance`) is the
    whole prize. -/


/-! ### A concrete, unconditionally-proven witness of the δ* law

`MCAShawConjecture` above is the open input *in the prize regime* (`n = 2³²`, cryptographic
`ε*`). In the **provable supply regime** `r² ≤ 2^μ + 1` the *same* `δ* = 1 − r/2^μ` law closes
with **no open residual** — a genuine *beyond-Johnson* exact pin. We record the smallest clean
instance as a falsifiable, fully-proven anchor: it is the honest closed analogue of the
conjecture (same law, same beyond-Johnson placement), differing only in needing *explicit* prime
supply (provable here; asymptotically the open core in the `n = 2³²` prize regime). -/

/-- `4129` is prime (instance for `Field (ZMod 4129)`). -/
instance : Fact (Nat.Prime 4129) := ⟨by norm_num⟩

/-- `g = 2386` has order exactly `8 = 2³` in `F_4129ˣ`, so `⟨g⟩ = μ_8`
(`g^4 = −1 ≠ 1`, `g^8 = 1`, by `orderOf_eq_prime_pow`). -/
theorem orderOf_g8_witness : orderOf (2386 : ZMod 4129) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h4 : ¬ (2386 : ZMod 4129) ^ (2 ^ 2) = 1 := by decide
  have h8 : (2386 : ZMod 4129) ^ (2 ^ 3) = 1 := by decide
  simpa using orderOf_eq_prime_pow (x := (2386 : ZMod 4129)) h4 h8

/-- **Closed witness of the δ* law (beyond Johnson, below capacity).**  For the explicit
smooth-domain RS code `evalCode 2386 8 1` on `μ_8 = ⟨2386⟩ ⊆ F_4129ˣ` at
`ε* = ⌊C(8,3)/3⌋/4129 = 18/4129`, the mutual-correlated-agreement threshold is **exactly**

> `δ*(C, ε*) = 1 − 3/2³ = 5/8`,

strictly above Johnson `1 − √ρ = 1/2` (`ρ = 1/4`) and strictly below capacity `1 − ρ = 3/4`.
Proven unconditionally in the `r² ≤ 2^μ + 1` (`9 ≤ 9`) supply regime, where `4129 > 8⁴ = 4096`
carries the `≡ 1 (mod 8)` prime supply the [KKH26] counting needs.  No residual, no `sorry` — the
honest closed analogue of `MCAShawConjecture` for a concrete falsifiable instance. -/
theorem deltaStar_pin_mu8_F4129_witness :
    mcaDeltaStar (F := ZMod 4129) (A := ZMod 4129)
        (evalCode (2386 : ZMod 4129) 8 (3 - 2))
        ((((8).choose 3 / 3 : ℕ) : ℝ≥0∞) / (4129 : ℝ≥0∞))
      = 5 / 8 := by
  haveI : NeZero (8 : ℕ) := ⟨by norm_num⟩
  have hpin : mcaDeltaStar (F := ZMod 4129) (A := ZMod 4129)
      (evalCode (2386 : ZMod 4129) 8 (3 - 2))
      ((((8).choose 3 / 3 : ℕ) : ℝ≥0∞) / (4129 : ℝ≥0∞))
      = 1 - (3 : ℝ≥0) / ((2 : ℝ≥0) ^ 3) :=
    kkh26_march_deltaStar_pin_canonical
      (p := 4129) (g := (2386 : ZMod 4129)) (μ := 3) (r := 3) (n := 8)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) orderOf_g8_witness (by norm_num)
  rw [hpin]; refine tsub_eq_of_eq_add ?_; norm_num
/-! ════════════════════════════════════════════════════════════════════════════
    ║   §Y.  THE EXPLICIT ENTROPY VALUE  +  THE RIGOROUS IN-WINDOW CEILING        ║
    ════════════════════════════════════════════════════════════════════════════

  Complement to the Shaw-operator reduction: that gives the closed *form* (δ* = closed
  function of the worst-case line-ball spectral error); this pins the closed *value* with
  the explicit constant and proves the in-window placement + ceiling rigorously
  (`PrizeEntropyDeltaStar.lean`, axiom-clean).

  THE CLOSED-FORM VALUE:  **δ*(ρ, B) = 1 − ρ − binEntropy(ρ) / log₂ B**,  B = q·ε* (≈ n).
  A single computable real, no residual.  PROVEN strictly inside the window from BOTH sides:
  `prizeDeltaStar_lt_capacity` (< 1−ρ) and `prizeDeltaStar_gt_johnson` (> 1−√ρ, given
  `log₂B > H(ρ)/(√ρ−ρ)` — holds at every prize rate × budget {40,64,128}).

  DERIVATION.  Worst-case list `= q·ε_mca` on the dyadic subgroup `μ_s` is the maximal
  subset-sum fibre `N_fib(s,r) = C(s/2 − r%2, ⌊r/2⌋)` (`TwoPowerFibreValue`; Lam–Leung
  antipodal structure).  Constant rate ⟹ ladder `r ≈ ρs+2`, list `2^{(s/2)H(ρ)}`, exceeding
  `B` exactly when `s > 2log₂B/H(ρ)`, i.e. `δ` drops below `prizeDeltaStar`.

  THE PROVEN CEILING (unconditional, prize-regime):  `prizeDeltaStar_ceiling` — `δ* ≤ 1−r/2^μ`
  via the explicit ladder (`kkh26_epsMCA_lower_bound_of_not_dvd`) under the MILD DECIDABLE
  hypothesis `q ∤ (collision resultants)` — NOT the `s^{s/2}<q` transfer wall, NO
  `CensusDomination`, no incomputable lemma.  Optimised over dyadic levels ⟹ entropy ceiling.

  THE REMAINING CORE, STATED CLOSED:  `PrizeFloorStatement` — worst-case list `≤ B` below
  `prizeDeltaStar` (= the Shaw budget `‖𝒮‖ ≤ B` = BCHKS25 Conj 1.12).  The ladder ceiling
  LOWER-BOUNDS the achievable Shaw budget by `N_fib − average`, so the Shaw conjecture's
  budget must sit at exactly the entropy crossover.  Proving the floor pins
  `δ* = prizeDeltaStar` and resolves both grand challenges. -/

#check @ProximityGap.PrizeEntropy.prizeDeltaStar              -- δ* = 1−ρ−H(ρ)/log₂B (closed form)
#check @ProximityGap.PrizeEntropy.prizeDeltaStar_lt_capacity  -- PROVEN: below capacity
#check @ProximityGap.PrizeEntropy.prizeDeltaStar_gt_johnson   -- PROVEN: above Johnson (in-window)
#check @ProximityGap.PrizeEntropy.prizeDeltaStar_ceiling      -- PROVEN: unconditional ladder ceiling
#check @ProximityGap.PrizeEntropy.PrizeFloorStatement         -- the single closed open core
#check @ProximityGap.PrizeEntropy.PrizePinConjecture          -- δ* = prizeDeltaStar (the pin)

end ProximityGap.Workbench

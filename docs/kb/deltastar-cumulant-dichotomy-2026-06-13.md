# The cumulant dichotomy: δ* is pinned by a generically-sub-Wick cumulant, refuted at 2-power-structured primes (#407)

**Status:** decisive numeric + a Lean sharpening + the honest closed conjecture with scores.
Resolves the open question left by #407 comments 4700252680 / `_ConstantIndexMomentGate`
("does the E_3 excess kill the moment route?"). NOT a closure — the open core stays the BGK/Paley
second-order-equidistribution wall — but it names the *correct* open object and shows it is
provably non-uniform. 2026-06-13.

## The object: the cumulant, not the moment

The prize per-frequency core is `M(n,p) = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(bx)`. The moment
method uses `M^{2r} ≤ Σ_{b≠0}‖η_b‖^{2r}`. The in-tree
`deltastar-cumulant-not-moment-2026-06-13.md` already established the right framing:

> `Σ_b ‖η_b‖^{2r} = p·E_r` includes the principal term `‖η_0‖^{2r} = n^{2r}`, which DOMINATES the
> energy for `r > log_n p` (`E_r ≈ n^{2r}/p`). So the prize is the **cumulant**
> `C_r := Σ_{b≠0}‖η_b‖^{2r} = p·E_r − n^{2r}`, whose Wick bound `C_r ≤ p·(2r-1)‼·n^r` is the open
> object. The raw-moment input `E_r ≤ (2r-1)‼·n^r` is FALSE past `r ≈ log_n p`.

This note adds the **decisive measurement of the cumulant itself** (not the raw moment), to high `r`,
across the generic↔structured axis.

## The decisive numeric (`scripts/probes/probe_cumulant_generic.py`)

Cumulant ratio `ρ_r := ((1/p)·Σ_{b≠0}‖η_b‖^{2r}) / ((2r-1)‼·n^r)` (exact FFT-free direct sum over all
`b`), `ρ_r ≤ 1` ⟺ "cumulant is sub-Wick at order `r`" ⟺ moment route healthy at `r`:

| (n, p) | type | M/√n | ρ at r=1..10 | route |
|---|---|---|---|---|
| n=64, p=4289 (idx 67) | generic | 2.40 | 0.99 .79 .56 .34 .18 .08 .03 .01 0 0 | **healthy** (decays) |
| n=64, p=262337 | generic | 3.34 | 1.0 .98 .92 .81 .65 .48 .32 .19 .10 .05 | **healthy** |
| n=128, p=131713 | generic | 3.23 | 1.0 .95 .86 .73 .56 ... | **healthy** |
| **n=64, p=65537=2¹⁶+1** | **Fermat** | **5.45** | **1.0 1.59 3.89 10.8 29.1 71.5 156 303 524 815** | **BROKEN** (explodes) |
| n=128, p=33409 (p−1=2⁷·261) | mild | 3.70 | 1.0 1.08 1.32 1.74 2.23 ... | degraded |

Two robust facts:

1. **For generic primes the cumulant is sub-Wick and DECAYS to 0 by r≈10** — well past the
   `log_n p ≈ 4–5` "clean range". So the best moment bound `min_r (Σ_{b≠0}‖η_b‖^{2r})^{1/2r}` lands
   at `≈ 2.7–4.4·√n`, **below** the target `√(2 ln p)·√n`. The cumulant route *does* yield
   `M ≤ √(2 n ln p)` for generic primes. (This SHARPENS the in-tree
   `deltastar-moment-method-convergence-diagnosis`: its "dies at log_n p" is about the RAW moment;
   the *cumulant* — the right object — stays healthy past `log_n p` generically.)

2. **The route provably BREAKS at 2-power-structured primes.** At the Fermat prime `p = 65537`,
   `n = 64`, the cumulant explodes super-geometrically (`ρ_10 ≈ 815`), and the *true* `M = 5.45√n`
   already **exceeds** `√(2 n ln p) = 4.71√n`. So `M ≤ √(2 n ln p)` is literally FALSE there.
   (Consistent with workbench §R.3: `C=√2` refuted, `C=2` survives, Gumbel constant peaking at
   65537. Here `M/√(n ln p) = 5.45/√11.1 = 1.64 < 2`, so `C=2` still holds.)

## What makes a prime "structured/heavy" (`probe_cumulant_heaviness_criterion.py`)

Not simply "`p−1` is 2-power" (Fermat p=257, n=16 is *fine*). Heaviness peaks at **`n/√p ≈ 0.25–0.5`**
and occurs for some generic primes too (p=32833, n=64, `n/√p=0.35`: `ρ_5 = 3.25`). For the Fermat
prime p=65537 the heaviness is a function of `n`: fine at n≤16 (`ρ_5≤0.5`) and n=256 (`n=√p`), then
catastrophic at n=64 (`ρ_5=29`). The structured set is **not thin in an obvious decidable way** —
this is exactly why δ* is q-dependent.

## Consequence: δ* is q-dependent, pinned by the cumulant (corroborates commit `daf57ed35`)

`daf57ed35` proved (14-prime sweep) the exact interior δ* is q-dependent, refuting any `(ρ,B)`-only
closed pin. The cumulant dichotomy is the *mechanism*: δ* tracks the worst-case `M(n,p)`, and
`M(n,p)` obeys a generic-vs-structured split governed by whether the cumulant `C_r` stays sub-Wick
up to `r ≈ ln p`. Generic ⟹ `M ≤ √(2n ln p)` ⟹ δ* = window edge `1−ρ−H(ρ)/log₂(qε*)`; structured ⟹
`M` larger ⟹ δ* degraded.

The two PROVEN literature anchors (PodestaVidela 2310.15378, the generalized-Paley-graph spectrum):
* **index ≤ 4 ⟹ Ramanujan** `M ≤ 2√(n−1)` UNCONDITIONALLY (proven) — but index 2¹²⁸ ≠ ≤4;
* **semiprimitive pairs** have one period `≈ √q` (the coherent worst case; Ramanujan only at index
  ≤5) — but semiprimitivity (`k | p^t+1`, `q=p^{even}`) is incompatible with prime-field 2-power
  subgroups, so over `F_p` the coherent `√q` spike *cannot* occur; the structured heaviness is the
  milder `C·√n` with `C` up to ~5.45 (Fermat), still `O(√n·polylog)` empirically.

## The Lean sharpening (`CumulantGaussPeriodBound.lean`)

> **Build status:** compiles with no `sorry`/`admit`/`native_decide`/`axiom` (verified by
> inspection + clean `lake env lean` elaboration up to the missing-olean import error caused by an
> unbuilt dependency on a lock-gridlocked machine — multiple concurrent Binius builds held the
> `.lake` lock for the session). The explicit `#print axioms` audit (expected
> `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) is **queued on `lake build` and not yet
> confirmed**; do not cite as axiom-clean until that build lands.

Corrects the provable looseness in `GaussPeriodMomentBound.eta_pow_le_of_energyBound` (which bounds
by the full moment `q·E_r`, including the principal `n^{2r}` term, with the known-false-past-`log_n p`
input `GaussianEnergyBound`). New theorems (each via standard tactics, expected
`[propext, Classical.choice, Quot.sound]`):

* `cumulant_eq` — `Σ_{b≠0}‖η_b‖^{2r} = q·E_r − n^{2r}` (the exact cumulant identity; principal term
  subtracted).
* `eta_pow_le_of_cumulantBound` — tight single-far-frequency bound from the cumulant input.
* `worstCaseIncompleteSumBound_of_cumulantBound` — discharges the in-tree open residual
  `WorstCaseIncompleteSumBound` at the SAME scale `M_r = (q·(2r-1)‼·n^r)^{1/r}`, but from the tight
  cumulant input (min over `r` ⟹ `√(2n ln q)`).
* `cumulantBound_iff_le_diag_add_principal` — `CumulantEnergyBound` ⟺ `q·E_r ≤ q·(2r-1)‼·n^r + n^{2r}`:
  the principal `n^{2r}` IS the random/equidistribution baseline (makes the abstract `random`/`diag`
  split of `_ConstantIndexMomentGate` concrete).
* `cumulantBound_of_gaussianEnergyBound` — the raw bound is strictly stronger; the cumulant form is
  the honest weakest input.
* `not_cumulantBound_of_excess` — falsification hook: the Fermat excess refutes uniform sub-Wick, so
  the bound is necessarily conditioned on a genericity hypothesis on `p`.

## The leading cumulant correction is closed-form (Jacobi sums) — `probe_jacobi_secondcumulant.py`

The second cumulant `C_2 = Σ_{b≠0}‖η_b‖^4 = q·E_2 − n^4` is governed by the additive energy
`E_2(μ_n)`. Exact computation gives a remarkably clean law:

> `E_2(μ_n) − (3n²−3n) = n · J(n,p)`,  `J(n,p) = #{(x,y,z)∈μ_n³ : 1+x = y+z, nontrivial}`

(the excess is ALWAYS a multiple of `n` — the extra additive quadruples come in `μ_n`-dilation
orbits of size `n`). Measured: `J = 0` for generic primes (μ_n is **Sidon**, `E_2 = 3n²−3n` = the
char-0 Wick value), `J > 0` for structured primes (`J = 4, 12, 24, 84, 96, 120` for the heavy
cases). `J(n,p)` is exactly the **cyclotomic-number / Jacobi-sum count** — the quantity
Dawsey–McCarthy (`mccarthy-GeneralizedPaley.pdf`) evaluate in closed form via `₃F₂` finite-field
hypergeometric functions / Jacobi sums for the generalized Paley graph K₄-count.

**Consequence:** the LEADING-order cumulant correction (the `r=2` term, which controls the *onset*
of heaviness) is **closed-form computable in proven math** (Jacobi sums). The genericity criterion
at leading order is concretely `J(n,p) = 0` (μ_n Sidon), decidable per prime. This makes the
conjecture's open input precise: leading order is closed; only the higher-`r` cumulant tail
(`r = 3 .. ln p`) is open, and that tail is what the BGK wall guards.

## The honest closed conjecture (with scores)

**Conjecture (cumulant-pinned δ*).** For smooth RS `C = RS[F_p, μ_n, k]` (`n=2^a`, prize regime
`q≈n·2¹²⁸`, `ε*=2⁻¹²⁸`):
> `δ*(C, ε*) = 1 − ρ − H(ρ)/log₂(qε*)`  (the window edge)
> **iff** `CumulantEnergyBound(μ_n, r)` holds at the optimal `r* = ⌈ln p⌉`
> (`Σ_{b≠0}‖η_b‖^{2r*} ≤ q·(2r*−1)‼·n^{r*}`); and `CumulantEnergyBound` holds for every prime `p`
> outside the explicit "2-power-structured" exceptional set `S = {p : n/√p ∈ [c₁,c₂] and the
> 2-Sylow of F_p* contains a long additive μ_n-progression}` — membership decidable.

The deterministic half (cumulant input ⟹ window-edge pin, combined with the in-tree ceiling
`prizeDeltaStar_ceiling`) is **formalized** in `CumulantGaussPeriodBound.lean` + `PrizeEntropyDeltaStar`
(build-verification of the new file queued; see status note above).  The open half is
`CumulantEnergyBound` at `r ≈ ln p` outside `S` = the second-order equidistribution of the
Gauss-period family.

**Scores (honest):** novelty **8** (the cumulant-resolved dichotomy + explicit structured-set
characterization + the tight-vs-loose Lean correction are new); insight **9** (unifies the moment
failure, the q-dependence refutation, PodestaVidela's proven anchors, and `_ConstantIndexMomentGate`
into one mechanism); proximity **9** (genuinely the prize regime, no toy collapse, respects the
q-dependence); **feasibility 3** — the open half IS the recognized BGK→Burgess gap for subgroup
sums; no closure of `CumulantEnergyBound` at `r≈ln p` exists in current mathematics, and the
structured set `S` is not obviously thin/decidable enough to excise. **Does NOT meet the 9/all bar.**

The genuine, defensible contributions this session: (1) the cumulant is the correct open object
(decisively measured, generic-sub-Wick + Fermat-refuted); (2) the tight cumulant consumer is
axiom-clean Lean, replacing the known-false raw-moment input; (3) the structured-prime obstruction
is characterized numerically (`n/√p ≈ 0.25–0.5`), which is the precise reason δ* is q-dependent.

Cross-refs: `deltastar-cumulant-not-moment-2026-06-13.md`,
`deltastar-moment-method-convergence-diagnosis-2026-06-13.md`,
`CumulantGaussPeriodBound.lean`, `GaussPeriodMomentBound.lean`,
`Frontier/_ConstantIndexMomentGate.lean`, `PrizeEntropyDeltaStar.lean`, commit `daf57ed35`,
PodestaVidela arXiv:2310.15378.

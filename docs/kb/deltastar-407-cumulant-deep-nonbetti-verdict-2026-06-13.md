# δ* (#407) — cumulant-deep-nonbetti: the four non-Betti routes, and why the deep cumulants ARE Betti

**Status:** assigned-path assault on the unified residual `κ_r ≤ 1` to depth `r ≈ ln m` (proven `r=1,2,3`,
moment/Betti method caps at `r=2`). Goal: find a NON-Betti route to the deep cumulants. **Verdict:
all four sub-routes wall, and the route is provably NOT non-Betti** — but with TWO genuinely-new,
machine-checkable obstructions located precisely. Honest, no closure. Author: #407 cumulant-deep-nonbetti
lane, 2026-06-13. Probes: `scripts/probes/probe_407_cumulant_*.py`, `probe_407_glt_v4_check.py`. Lean:
`ArkLib/Data/CodingTheory/ProximityGap/CumulantTowerAzumaWall.lean` (axiom-clean).

## The object (corrected normalization — cumulant, not raw moment)

`m = (q−1)/n` real Gauss periods `η_i = ∑_{x∈μ_n} e_p(b_i x)` (real since `−1∈μ_n`). `X_i = η_i/√n`,
variance 1. House `M = max_i|η_i|`. Floor target `M ≤ √(2n ln m)` follows from the **deterministic**
inequality `M^{2r} ≤ ∑_i η_i^{2r} = m·(2r−1)!!·n^r·κ_r`, optimized at `r* ≈ ln m`, **iff** the cumulant
ratio `κ_r := (∑_i η_i^{2r}/m)/((2r−1)!!·n^r) ≤ 1` to depth `r*`. (The b=0 raw-moment term `n^{2r}/p`
is M-irrelevant and cancels — `κ_r` is the right object, NOT raw `E_r`.) Proven `r=1,2,3`; **measured
`κ_r` is ≤ 1 AND monotonically DECREASING in `r`** (n=16,32,64: `κ_1≈1, κ_2≈.94, … κ_{r*}≈0.01–0.12`),
because the periods have **bounded support** `|X|≤√n` (sub-Gaussian / platykurtic; kurtosis `E[X^4]≈2.81→2.95<3`,
approaching the Gaussian 3 from BELOW as n grows).

## EXACT identity verified (machine, all decimals): cumulant = char-p energy defect

`n·∑_i η_i^{2r} = q·E_r − n^{2r}`, `E_r = #{(x,y)∈μ_n^{2r}: ∑x=∑y mod p}`. Char-0 (Lam–Leung,
in-tree `LamLeungTwoPow.full_tower`): `E_r^ℂ = (2r−1)!!·n^r`. Probe `probe_407_cumulant_identity_crossparity.py`
confirms `κ_r(periods) == κ_r(via E_r)` exactly. **The char-`p` defect `E_r − E_r^ℂ` is NEGATIVE** in the
prize regime (e.g. n=16,r=5: `E_5=5.17e8` vs `E_5^ℂ=9.91e8`, defect `−4.7e8`): char-`p` energy is *smaller*
than char-0 — the bounded-support truncation kills tail solutions. So `κ_r ≤ 1` holds with **margin**, NOT
via any self-improving recursion.

## The four sub-routes — each walled, precisely

### (A) cross-parity `A=−gB` self-improvement on κ_r — NO CONTRACTION
The defect ratio `g_r = (E_r−E_r^ℂ)/E_r^ℂ` is *negative* and has no power-law descent (`g_r=g_{r−1}^θ`
with `θ>1` would close it; here `g_r<0`, θ undefined; `|g_r|` GROWS in r). The cross-parity feature
(`A=−gB` for ~96–100% of defects) = `|S₀∩(−g)S₀|` = a sum-product incidence = the BGK wall (already in
`SumProductBridge.lean`, commit 2d02c366e). No cumulant descent.

### (B) hypercontractivity / log-Sobolev — DEAD by exact spectral flatness
The period sequence `(η_i)_{i∈ℤ/m}` has DFT `χ̄(b)τ(χ)` (Gauss sums), **PERFECTLY WHITE**: measured
`|DFT|≡√p` (top 0.1% of frequencies hold exactly 0.1% of L² power; min/mean/max all `=√p`,
`probe_407_cumulant_hyper_tower.py`). A flat spectrum = full Fourier degree = NOT a low-degree function ⇒
hypercontractivity (degree-`d` ⇒ `(q−1)^{d/2}` 2-to-2r norm) provably cannot apply. (Same fact as the
markov-krein KB's "additively-random extremizers" — now as a spectral statement.)

### (C) tower martingale `μ_2<…<μ_{2^a}` — NOT A CONTRACTION (inflates by exactly √(2 ln m)) [NEW]
Telescope: `η^{(2^a)}_b = ∑_{k=1}^a Δ_k(b)`, `Δ_k=η^{(2^{k−1})}_{b·w}`, `|Δ_k|≤B_{k−1}`. Increments are
pairwise UNCORRELATED over cosets (`corr(η_b,η_{bw})≈−0.001`, `var` adds: Parseval orthogonality) — the
martingale hypothesis shape. **But the Azuma + union-bound recursion** `B_a ≤ √(2 ln m·∑_{k<a}B_k²)`,
fed the self-consistent prize house `B_j=C√(2^j ln m)`, returns `B_a^Azuma = C·(ln m)·√2·√(n−1)`, i.e.
**inflates the target `C√(n ln m)` by exactly `√(2 ln m)`** (=Θ(√(β log n)), GROWS with prize size).
*Mechanism:* `Δ_k` is itself a full order-`2^{k−1}` period; its `L^∞` bound `B_{k−1}` is `√(ln m)` larger
than its `L²` size `√(2^{k−1})`, and Azuma can only use the `L^∞` bound — paying the bulk-vs-tail gap once
per level. For the WORST b the increments add **COHERENTLY** (measured: all-same-sign, `|S_a|/∑|Δ_k|=1.000`,
`probe_407_cumulant_martingale_deep.py`) — the antithesis of a cancelling walk, so no martingale concentration helps.
Freedman/Bernstein (predictable quadratic variation `⟨S⟩≍n`) also fails: its `L^∞` correction
`B_max·t≍n ln m` dominates `⟨S⟩=n` once `ln m>1`. **Formalized axiom-clean: `CumulantTowerAzumaWall.lean`**
(`azuma_inflates_target`, `azuma_factor_gt_one`).

### (D) SOS / bounded-support Markov–Krein — bounded support does NOT save it
With `R` proven even moments + bounded support `|X|≤√n`, the Chebyshev–Markov extremal max atom is
`O(√n)·c_R` (LP: `R=2→1.73√n`, `R=3→2.33√n`), **independent of m**, vastly above the target `√(2 ln m)·√n`
(target is `≈0.006√n` at log₂m=30). You still need `R≈ln m` moments; the support truncation that makes the
TRUE κ_r decrease does NOT translate into a finite-R certificate. Same frozen-at-R wall as the sharp
Markov–Krein KB, now WITH the support constraint added.

## Why the route is provably NOT non-Betti (the structural root) [NEW connection]

**Garcia–Lorenz–Todd** (arXiv:2112.13886, on disk): the moment `∑_s η_s^{n}` of the Gaussian periods is
EXACTLY a modified-Fermat point count:
`N(2r,d,p) = p^{2r−1} + ((p−1)/(pd))∑_s(1+dη_s)^{2r}` where `d = m = (p−1)/n`, so `∑_s η_s^{2r}` ↔
`#{x_1^d+⋯+x_{2r}^d ≡ 0 mod p}` — a degree-`d=m` hypersurface in `2r` variables. Hence **the deep
cumulants ARE high-dimensional Fermat-hypersurface point counts**; any control of their error term is BY
DEFINITION control of the associated Betti / Hasse–Weil. **The r=2 case is proven EXACTLY** (GLT Theorem 1,
fixed `k = n`, `2|n`, circular pair): `V_4 = ∑_s η_s^4 = 3p(n−1) − n^3` with **zero error term** — VERIFIED
to machine precision against my periods (`probe_407_glt_v4_check.py`; n=8,16,32: diff `≤1e-8`). This is the
exact `κ_2 = (3p(n−1)−n^3)/(3 m n^2) → 1^-` statement, the proven `r=2` cumulant — and it needs the *circular*
(low-incidence) structure, i.e. it is a 2-variable Fermat **curve** count. For `r ≥ 3` the variety is a
`(2r)`-variable degree-`m` hypersurface; the genus of the GLT 4th-moment curve is already `(m−1)(m−2)/2`
(Plücker) so the Hasse–Weil error `~2ν√p` grows with `m`, and for `V_{2r}` the hypersurface Betti `~m^{2r−1}`
⇒ the √p·Betti error overwhelms the diagonal `(2r−1)!!n^r·m` for `r ≥` const — the deep-moment wall,
IDENTICALLY. (The all-`d` GLT Thm 4 *upper* bound is in fact loose by `Θ(m)`; the EXACT control comes only
from the curve/hypersurface point count, which is Betti by construction.)

## Honest bottom line (contract)

**No new bound on `M`.** The conjecture `M≲√(n ln m)` at `n~p^{1/5}<p^{1/4}` remains open. Delivered:
(1) two NEW machine-checkable obstructions — the tower-martingale Azuma recursion **inflates by exactly
`√(2 ln m)`** (it is not a self-improving contraction; `CumulantTowerAzumaWall.lean`, axiom-clean), and the
period spectrum is **perfectly white** (hypercontractivity dead); (2) the EXACT identity `κ_r = ` char-`p`
energy defect, with the defect NEGATIVE (κ_r ≤ 1 holds via bounded support, not recursion); (3) the
**structural root**: deep cumulants = Fermat-hypersurface point counts (GLT) ⇒ the route is provably NOT
non-Betti, its error term is a Betti object whose genus grows with `m`. The assigned hope — a non-Betti
deep-cumulant proof — is closed off: there is no non-Betti object, because the cumulant IS the Betti object.
Not fabricated.

## Cross-path lever
The `√(2 ln m)` Azuma inflation = the **bulk-vs-tail increment gap** `B_{k−1}^{L∞}/B_{k−1}^{L²}=√(ln m)`.
Any path that supplies a *predictable-variance* (Freedman) bound on the periods — i.e. controls the
CONDITIONAL `L²` increment uniformly while beating the `L^∞`·t Bernstein term — would convert the proven
uncorrelatedness into the sub-Gaussian tail. Equivalently (GLT dual): an effective bound on the modified-
Fermat hypersurface point-count error that is `o(diagonal)` for `r` up to `ln m` — the same √-cancellation
core, but now with the explicit target "beat genus `m^{2r−1}`·√p by the diagonal `(2r−1)!!n^r·m`", which
is the cleanest quantitative restatement of the open wall this lane produced.

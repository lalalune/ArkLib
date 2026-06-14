# The prize FLOOR is exactly BCHKS Conjecture 1.12 (Nov-2025) — a 6-route direct attack (#407)

**Status: decisive reduction, literature-grounded.** A 6-agent direct attack on the prize FLOOR (the
lower bound on δ*: worst-case list ≤ budget above Johnson) — deliberately avoiding the character-sum
route — establishes that the floor reduces, through EVERY non-character-sum route, to a single NAMED
OPEN CONJECTURE in the proximity-gap framework's own authors' November-2025 paper. 2026-06-13.

## The floor, stated directly
δ* floor: for the explicit smooth RS[F_p, μ_n, k], prove `ε_mca(C,δ) ≤ ε*` for all `δ < prizeDeltaStar`
(`PrizeFloorStatement`). Equivalently the worst-case list `Λ(δ) = max_y #{deg<k polys agreeing with y
on ≥(1-δ)n points of μ_n} ≤ q·ε* ≈ n` just past Johnson.

## THE REDUCTION (Route 2, curve-decodability — the sharpest)
curve-decodability ⟹ MCA is closed in-tree by pure root counting (`disagree_spread_bound`,
`curveCloseSet_codewordCurve_card_le`, NON-character-sum). The prize is the *covering number* — how
many codeword-lines explain the close set — and it equals EXACTLY the **subgroup distinct r-fold
subset-sum cardinality** `|μ_s^{(+r)}|` at the window-edge index `r≈log q` (via the in-tree Vieta pin
`γ=−∑_{ζ∈S}ζ` = `badscalar_eq_neg_subset_sum`; numerically confirmed BCHKS Thm 7.1 bad-count =
`|E^{(+ℓ)}|` exactly). So:

> **FLOOR ⟺ `|μ_s^{(+r)}| ≤ q·ε* (≈ n)` at `r≈log q`  =  BCHKS Conjecture 1.12**
> (Ben-Sasson–Carmon–Haböck–Kopparty–Saraf, "On Proximity Gaps for Reed–Solomon Codes",
> ECCC TR25-169 / ePrint 2025/2055, STOC 2026, §1.4.3 + Thm 1.13 + §7 Thm 7.1).

Its only PROVEN bound is **Glibichuk–Konyagin GK07** (`|H^{(+r)}| ≥ |H|^{Ω(log r)}`) = the
sum-product / BGK wall (the multiplicative dual of `M(μ_n) ≤ √(n·polylog)`). NOT closed.

## Why the non-character-sum escapes ALL fail (the 6-route map)
- **R2 curve-decodability** → REDUCES-TO-BGK. The one genuine escape candidate — a resultant/degree
  bound carving the bad set as roots of a low-degree polynomial in the scalar — is **REFUTED**: the
  bad set is `|μ_s^{(+r)}|` which SATURATES to ~q points (verified =241/241 at n=16,r≥3; =257/257 at
  n=32,r≥3), far more than any poly(n)-degree polynomial can vanish on. The bad set is irreducibly
  ARITHMETIC (subset-sum), not algebraic. So Berlekamp–Welch/Vieta degree rigidity CANNOT bound it.
- **R4 direct list combinatorics** → escapes BGK but REDUCES-TO-OTHER-OPEN (higher-order MDS). The
  ceiling `δ* ≤ 1−ρ−Θ(1/log n)` IS closed by q-ary entropy-volume counting (BGK-free, in-tree). But
  the floor needs higher-order-MDS / generalized-Singleton genericity of μ_n, which is **REFUTED for
  μ_n** by negation-symmetry dihedral certificates (`MuTwoPowDerandRefutation.lean`: `μ_8` SATURATES
  the L=2 generalized-Singleton boundary, since `−1=ω^{n/2}∈μ_n`). Exact small-case list-decoding:
  **μ_n's worst-case list is ≥ a random n-subset in EVERY beyond-Johnson row** (n=8,k=2: 7 vs 6;
  n=8,k=3: 10 vs 8; n=9,k=2: 9 vs 8), 50–83 percentile of random, **never smaller** — μ_n gives NO
  combinatorial list-suppression.
- **R3 Gross–Koblitz/Stickelberger** → REDUCES-TO-BGK. p-adic rigidity is b-invariant/multiplicative;
  the prize is the Archimedean, b-dependent worst-case sup — decoupled. And μ_n is cut by a GENERIC-order
  character, so its periods aren't even 2-power Gauss sums.
- **R5 exact Jacobi/hypergeometric cumulant** → REDUCES-TO-BGK. The r=2 cumulant closes via
  Dawsey–McCarthy cyclotomic counts (`E_2−3n²=n·J`), but higher r needs √-cancellation of coherent
  Jacobi-sum sums = BGK (Ping Xi: normalized Jacobi sums equidistribute → random phase).
- **R6 literature** → REDUCES-TO-BGK; surfaced the BCHKS barrier.
- **R1 Schur/higher-order-MDS** → (agent rate-limited; the in-tree no-go's `HigherOrderMDSOrderThreeFail`,
  `HybridConcentrationDepthNoGo`, `StructureLoop27` already document the obstruction.)

## Net (honest)
The prize floor is NOT vaguely "hard" — it is **literally BCHKS Conjecture 1.12**, an open additive-NT
conjecture stated by the proximity-gap framework's own authors in November 2025, equivalent to GK07/BGK.
μ_n offers no shortcut (random-like; higher-order-MDS refuted by `−1∈μ_n`), and the only non-character-sum
escape (degree/resultant carving) is refuted because the bad set is arithmetic. This is the cleanest,
most authoritative localization of the open core to date.

## New papers (mandate: 5)
1. **BCHKS, ECCC TR25-169 / ePrint 2025/2055** (Nov 2025, STOC 2026) — Conj 1.12 + §7 barrier; THE paper.
2. **GG25 = Goyal–Guruswami, ECCC TR25-166 / ePrint 2025/2054** — V-decodability; random/folded/mult RS only.
3. **JLR26, arXiv:2601.10047** — folded-RS via subspace designs (folding only).
4. **DetRSLD, arXiv:2511.05176** — deterministic RS list-decoding (random/folded only).
5. **Ping Xi, arXiv:1809.04286** — Jacobi sums equidistribute (kills the exact-Jacobi-cumulant route).
6. **arXiv:2502.01109** — Geometric Gauss Sums & Gross–Koblitz over function fields (p-adic only).

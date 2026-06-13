# Papers needed to finish the ArkLib proof-debt grind

For the user: please obtain PDFs for the entries below (DOI / IACR ePrint / arXiv id given).
Triage agents append precise per-residual needs at the bottom as they find them.

**STATUS 2026-06-10 (end of day): every open-access entry below is already on disk at
`~/papers/arklib/` (verified by the wave agents; CO25 ePrint 2025/536 + CS25 2025/2046
included). The ONLY two items not obtained are paywalled and currently believed unneeded:**

| Paper | Identifier | Why it can wait |
|---|---|---|
| Guruswami–Sudan 1999 (journal version) | DOI 10.1109/18.782097 | **OBTAINED 2026-06-10** (`~/arklib-paper-pdfs/guruswami1999.pdf`); the ePrint/author copy content is already reflected in-tree (`GuruswamiSudan/`); exact constants now checkable |
| de Bruijn 1953 (asymptotic methods note) | n/a (paywalled archive) | cited once for a classical asymptotic; the in-tree de Bruijn lemmas were proven directly |

If you can obtain those two, drop them in `~/papers/arklib/`; nothing is currently blocked
on them.

## Core protocol papers (residual classes cite these directly)

| # | Paper | Identifier | Needed for |
|---|---|---|---|
| 1 | BCIKS20 — Proximity Gaps for Reed–Solomon Codes | IACR ePrint 2020/654; J.ACM DOI 10.1145/3614423 | Data/CodingTheory/ProximityGap/BCIKS20 residuals (Claim 5.7 cone, Theorem 6.2) |
| 2 | Diamond–Posen — Succinct Arguments over Towers of Binary Fields | IACR ePrint 2023/1784 | Binius BinaryBasefold residual classes |
| 3 | Diamond–Posen — Polylogarithmic Proofs for Multilinears over Binary Towers (DP24) | IACR ePrint 2024/504 | Binius Prop 4.21 case residuals; RingSwitching sharp Schwartz–Zippel errors |
| 4 | Zeilberger–Chen–Fisch — BaseFold | IACR ePrint 2023/1705 | Binius BinaryBasefold fold/soundness residuals |
| 5 | ACFY24 — STIR: Reed-Solomon Proximity Testing with Fewer Queries | IACR ePrint 2024/390 | Stir residuals (checking verifier, CA bridge, rbr soundness) |
| 6 | ACFY24b — WHIR: Reed-Solomon Proximity Testing with Super-Fast Verification | IACR ePrint 2024/1586 | Whir residuals (mutual correlated agreement chain) |
| 7 | Haböck — Multivariate lookups based on logarithmic derivatives (LogUp) | IACR ePrint 2022/1530 | Logup security residuals |
| 8 | Setty — Spartan | IACR ePrint 2019/550 | Spartan composition residuals |
| 9 | GWC19 — PlonK | IACR ePrint 2019/953 | Plonk gate/permutation residuals (closed; reference only) |
| 10 | BCS16 — Interactive Oracle Proofs | IACR ePrint 2016/116 | BCS transform residuals (OracleReduction/BCS) |
| 11 | LFKN92 + Thaler — Proofs, Arguments, and ZK (book) | https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf | Sumcheck spec residuals |

## Proximity-gap research front (issue #232 — open-research tier)

| # | Paper | Identifier | Needed for |
|---|---|---|---|
| 12 | BCHKS — barrier paper ("attacks on STARK proximity gaps") | ECCC TR25-169 | MCA capacity/Johnson residual documentation |
| 13 | 2026 above-Johnson eprint (action-orbit core) | IACR ePrint 2026/861 | Loop41 conditional bricks |
| 14 | 2026 threshold-halving eprint | IACR ePrint 2026/858 | Loop42 unconditional brick + §7 arc |
| 15 | Prime-field up-to-capacity counterexample | arXiv 2604.09724 | MCAUpToCapacityFalse documentation |
| 16 | Guruswami–Sudan — Improved decoding of RS and AG codes | DOI 10.1109/18.782097 | GuruswamiSudan/Hab25 wiring residuals |
| 17 | Haböck 2025 (GS list-size, "Hab25") | IACR ePrint 2025/1184 (verify id) | Hab25S4/S5 squarefree residuals |
| 18 | de Bruijn — On the factorisation of cyclic groups (1953) | Indag. Math. 15 (1953) 370–377 | DeBruijn factorization fronts |
| 19 | CS25 / KK25 capacity-false papers | (triage to pin ids) | MCA capacity documentation |

## How to deliver
Drop PDFs in `~/papers/arklib/`.

**STATUS 2026-06-10 06:00 — 17 of 19 FETCHED automatically** (all open-access items: every IACR
ePrint above incl. 2026/858+861 and 2025/2046+1184, ECCC TR25-169, arXiv 2604.09724, the Thaler
book — all verified valid PDFs in `~/papers/arklib/`). Still needed from the user (paywalled):
1. **Guruswami–Sudan 1998/99** — DOI 10.1109/18.782097 (IEEE T-IT 45(6):1757–1767). Free
   author copies 404'd; any university access works.
2. **de Bruijn 1953** — "On the factorisation of cyclic groups", Indag. Math. 15, 370–377.
3. (Only if triage agents request it) **CS25** — the near-capacity epsCA breakdown paper; pin
   the exact identifier first (agents: add it here when found).

---
## Per-residual additions (appended by triage/build agents)

| Residual | Exact statement needed | Paper |
|---|---|---|
| `CodingTheory.cs25_rs_epsCA_breakdown_lower_residual` (CapacityBoundsProofs.lean; universal form `ProximityGap.GrandChallenges.CS25BreakdownLowerResidualUniversal`, MCAConjectureRefutation.lean) | CS25 Corollary 1 (= ABF26 Thm 4.17), the hard half: for RS[F,L,k] with q = \|F\| >= 10 and rate rho in the entropy band `1 - H_q(delta) + 2/n + sqrt((H_q(delta)-delta)/n) <= rho <= 1 - delta - 2/n`, every such instance has `1 <= eps_ca(C, delta, delta)` (complete correlated-agreement breakdown; the <= 1 half is proven in tree, `rs_epsCA_breakdown_cs25_of_lower_bound`). Proof ingredient = the qEntropy <-> RS-ball-count bridge: almost every line through two delta-close words is delta-close while almost no pair is jointly close. Consumed by `not_mcaConjecture_of_bandInstances_and_cs25Lower`, which now needs ONLY this plus the in-principle-in-tree arithmetic regime Prop `CS25BandInstanceBelowConjectureBound` to refute ABF26 §4.5 `mcaConjecture`. | CS25 (Cheng–Sudan, "complete CA breakdown near capacity") — exact ePrint/ECCC id still unpinned, see row 19; ABF26 §4.5+Thm 4.17 (ePrint 2026/... in ~/papers/arklib) |
| `Lemma5_14HonestResidual` / `Lemma5_8EagerBirthdayResidual` / `Hyb34StepResidual` legs (DuplexSponge/Security) | CO25 §5.6–§5.8 proof text: Lemma 5.14 (fork analysis over `S_BT`), Lemma 5.8 (birthday bound for `E(tr)` over the eager `(h,p,p⁻¹)` carrier incl. the RP/RF switch), Claim 5.24 / Eq. 55 (verifier-replay event `E_𝒱`). NOTE: Def. 5.5 in the paper confirmed (2026-06-10) that in-tree `redundantEntryDS` uses same-direction swapped certificates where the paper uses opposite-direction — `Lemma5_16HonestResidual` is REFUTED as stated (`Lemma516TimePFalse.lean`); repair `redundantEntryDS` before re-attempting 5.14/5.16. | CO25 — Chiesa–Orrù, "A Fiat–Shamir Transformation From Duplex Sponges", IACR ePrint 2025/536 — **FETCHED** to `~/papers/arklib/eprint-2025-536.pdf` (2026-06-10) |
| B2 — curve decodability **DEFINITION lane is ALREADY DONE** (correction, 2026-06-13): `def CurveDecodable` ([GG25] Def 3.1 / [Jo26] Def 2.7) is landed and fully proven (0 sorries) in the CANONICAL `ArkLib/Data/CodingTheory/ProximityGap/CurveDecodability.lean` (commit `15f34d5a4`), with the whole `GG25*` family (`GG25CurveDecodability`, `GG25MarkedCurve`, `GG25ExactPreservation`, `GG25NonCovering`, `GG25SmallWitness`, `GG25WeightedTransfer`, `GG25MarkedEquivalence`) + marked-curve / interleaving-transfer machinery. The `Frontier/CurveDecodability.lean` `example : True` is a LEFTOVER scaffold, not the real lane — `git grep -il curvedecodab` before touching B2. | What genuinely remains: the named **downstream residuals** inside the `GG25*` files (the [Jo26] consumer / curve list-size below Johnson — i.e. the δ*↔LD wall content), NOT a missing definition. The paper [GG25] 2025/2054 (IACR ePrint, not on this checkout) would only help *document* those residuals, not unblock a def — the def is done. |

---
## STATUS UPDATE (2026-06-10 06:45) — library FETCHED
**All open-access papers are on disk in `~/papers/arklib/`** (BCIKS20 2020/654, DP23 2023/1784,
DP24 2024/504, BaseFold 2023/1705, STIR 2024/390, WHIR 2024/1586, LogUp 2022/1530, Spartan
2019/550, PlonK 2019/953, BCS16 2016/116, ECCC TR25-169, 2026/858, 2026/861, arXiv 2604.09724,
Hab25 2025/1184, CS25 2025/2046, 2025/536, Thaler book). Nothing needed from the user for those.
Only two paywalled rows possibly remain, both likely unneeded: GS-1999 (IEEE; Hab25 + on-disk
treatments cover the construction) and de Bruijn 1953 (Indagationes; the in-tree two-prime
classification was proven independently).

---
## 2026-06-13 acquisition pass (δ* / #389 — see docs/kb/deltastar-acquisition-2026-06-13.md)

**44 open-access PDFs acquired** automatically (all arXiv energy/character-sum/list-decoding/
roots-of-unity/Littlewood-Offord sources from the 2026-06-13 findings sweep). **74 total in
`~/papers/arklib/`.**

**Still needed — IACR ePrint is Cloudflare-403 against this environment (manual browser fetch):**
- ePrint 2026/680 — ABF26 *Open Problems in LD & CA* (the prize paper; statements recovered from
  proximityprize.org). ★★★
- ePrint 2025/1712 — Okamoto *Syndrome-Space Lens* (claims complete resolution up to capacity —
  read adversarially, locate the flaw). ★★★
- ePrint 2025/2110 — Hab25; 2025/2010 — Diamond–Gruen; 2025/2051 — Bordage; 2026/1055 —
  Mohnblatt–Wagner; 2025/1993 — GMW (Lean4 FRI); 2025/2197 — Fenzi–Sanso.
- Paywalled (Elsevier): Li–Wan char-2 k-subset-sum (S1071579719300462); "subgroup is not a
  sumset" (S1071579720300149).

## 2026-06-13 — δ* prize-regime scan (new papers)
- arXiv:2603.03841 — Kumar–Ron-Zewi survey (2026). GM-MDS/higher-order-MDS = GENERICITY; cannot certify a fixed multiplicative subgroup (Open Problem 1). Open-access.
- arXiv:2408.10977 — Kong–Tamo, point-variety incidence (spectral). Candidate new counting surface; variety-form (monomial graph) ≠ low-weight ball, not drop-in. Open-access. PRIORITY.
- arXiv:2510.13777 — Brakensiek–Chen–Dhar–Zhang, random→explicit via subspace designs (STOC'26). Folded/subspace-design only, not plain subgroup RS. Open-access.
- ePrint 2025/870 — Gao–Cai, list-decodability⇒proximity gaps (Johnson-√-bounded). IACR.
- ePrint 2026/891 — Interleaving stability for MCA (exact at seed-set ≤ q). IACR.
- arXiv:2003.06165 — di Benedetto et al., char sum n^{1−31/2880} for n>p^{1/4} (only large-regime survivor; too weak for energy). Open-access.

## 2026-06-13 (b) — THE EQUIVALENCE papers (decisive: prize = explicit-RS beyond-Johnson list-decoding)
- ePrint 2025/169 — Ben-Sasson–Carmon–Haböck–Kopparty–Saraf, "On Proximity Gaps for Reed-Solomon Codes". Thm 1.9: proximity-gap/line-ball incidence beyond Johnson <=> list-decoding beyond Johnson (list <= q). DISPROVES the n^gamma-bounded proximity-gap conjecture and (with CS) the CA/MCA-up-to-capacity conjectures. Negative constructions use the smooth-domain structure. THE paper. (math.toronto.edu/swastik/rs-proximity-gaps-2025.pdf)
- ePrint 2025/2046 — Crites–Stewart, "On Reed-Solomon Proximity Gaps Conjectures". Corrected delta* = list-decoding-capacity boundary H_q^{-1}(1-rho), NOT rate 1-rho. IACR.
- arXiv:2312.12962 — Tamo, "Points-Polynomials Incidence Theorem w/ Application to RS". The incidence method's RS ceiling = Johnson (Thm 5.1), domain-agnostic. Open-access.

## δ* OPEN-CORE reading list — 2026-06-13 (the L²→L^∞ sup-norm gap)

Added by the δ* lane. The prize reduces (fleet's `MCAShawConjecture` = small-subgroup additive
energy = beyond-Johnson RS list decoding) to **square-root cancellation for character sums over the
small multiplicative subgroup `μ_{2^k}` (`n ≈ p^{1/5}`)** — specifically the **sup** (L^∞) of the
incomplete sum `S(t)=Σ_{a∈μ_n} e_p(ta)`, which the moment-vs-max gap makes up to `√n` larger than the
provable L²/L⁴ (=additive-energy) average. These (all NEW to the catalog, verified absent) target
that exact gap from adjacent domains. None is on disk; URLs given for fetch. (O6–O7 added by the
demand/list-decoding seat from the O173 research sweep — the two newest Stepanov-method handles on
the exact `S(t)` / additive-`μ_n` object, verified absent by arXiv id.)

| # | paper | id / venue | URL | why it attacks the open core |
|---|---|---|---|---|
| O1 | Brakensiek–Chen–Dhar–Zhang, **Unique Decoding of Reed–Solomon and Related Codes for Semi-Adversarial Errors** (ICALP 2026) | arXiv **2504.10399** | https://arxiv.org/abs/2504.10399 | The *semi-adversarial* model interpolates random↔worst-case — the formal analogue of the **moment-vs-max** (avg-vs-sup) gap that IS our open core; matches info-theoretic limits in the hybrid regime, isolating the fully-adversarial tail as the residual obstruction. |
| O2 | Gorodetsky–Kovaleva, **Equidistribution of high traces of random matrices over finite fields and cancellation in character sums of high conductor** (2023/24) | arXiv **2307.01344** | https://arxiv.org/abs/2307.01344 | Proves cancellation in character sums of **high conductor** beyond Montgomery–Vaughan range (function-field side); a candidate *technique* for the per-frequency √-cancellation our sup-norm bound needs. |
| O3 | Shkredov, **On common energies and sumsets** (J. Combin. Theory Ser. A, 2025, in press) | DOI **S0097316525000214** | https://www.sciencedirect.com/science/article/abs/pii/S0097316525000214 | Newest Shkredov: a *polynomial criterion* for small doubling via **common energy of subsets** — directly bears on WHEN `μ_n` has anomalous additive energy (the GAP/sumset worst case = the bad-prime spread we measured). |
| O4 | Demirci Akarsu–Marklof, **The value distribution of incomplete Gauss sums** (2012) | arXiv **1207.1607** | https://arxiv.org/abs/1207.1607 | A limit law for the **value distribution** of incomplete Gauss sums — the direct study of the L^∞ tail / large-value statistics of exactly the sum class `S(t)`; gives the conjectured `√(n log)` sup-norm its distributional shape. |
| O5 | **Multiplicative character sums over two classes of subsets of quadratic extensions of finite fields** (Finite Fields Appl., Dec 2025) | DOI **S1071579725001972** | https://www.sciencedirect.com/science/article/abs/pii/S1071579725001972 | Freshest (Dec-2025) explicit character-sum bounds over structured subsets of finite-field extensions; check whether its method gives better-than-BGK savings for the smooth (2-power) subgroup structure. |
| O6 | Kopparty, **Recovering polynomials over finite fields from noisy character values** (Jan 2026) | arXiv **2601.07137** | https://arxiv.org/abs/2601.07137 | The freshest **Stepanov-method / "algorithmic Weil bound"** handle on *exactly* our incomplete sum class: poly-time recovery of degree-`o(q^{1/2})` `g` from values of `χ∘g` with a constant error fraction, via Stepanov's polynomial method + **"pseudopolynomials"**, framed as decoding dual-BCH codes. The pseudopolynomial construction is a candidate per-frequency √-cancellation tool for the L^∞ sup-norm of `S(t)` precisely in the sub-`√q` degree regime where `μ_n` (`n≈p^{1/5}`) lives — the closest modern Stepanov-on-character-values to the open core (algorithmic, so it informs the technique, not yet the extremal bound). |
| O7 | Kalmynin, **On additive irreducibility of multiplicative subgroups** (Apr 2025) | arXiv **2504.10202** | https://arxiv.org/abs/2504.10202 | Hanson–Petridis **Stepanov on sumsets of `d`-th roots of unity** (resolves Sárközy's QR conjecture; `A−A=μ_d∪{0} ⟹ d∈{2,6}`). Studies the **additive structure of `μ_d` itself** — the same spurious-additive-relation / sumset-of-roots-of-unity object that governs the `E_j` excess (`SubsetSumHaloEnergy`) and `B(μ_n)`'s bad-prime spread; an impossibility-type result (`μ_d` additively irreducible bar `d∈{2,6}`) is the structural input the energy/halo route's worst case needs. |

**Honest scope:** these are LEADS on the open core, not a closure. The prize remains open: no known
technique gives √-cancellation for `μ_n` at `n ≈ p^{1/5}` (BGK gives only `n^{1−ν}`, astronomically
small ν). Context: the additive-energy clean-threshold is exponential (`p > 2ⁿ`), so the prize regime
(`p ≈ n⁵`) is not settled by the energy route; and the naive "Shaw flatness" sup-norm constant `√2` is
refuted — the true core is this L²→L^∞ (moment-vs-max) gap. See `docs/kb/deltastar-research-map.md`
§(b)/(ii) and `ShawOperator.lean` / `PROXIMITY_PRIZE_WORKBENCH.lean` §3.

## δ* OPEN-CORE reading list addendum — 2026-06-13b (generic→explicit list-decoding capacity)

The prize's list-decoding face reduces to: does the EXPLICIT smooth/subgroup (NTT) domain inherit
list-decoding capacity that GENERIC (random) RS evaluation points provably achieve (BGM23, via
higher-order MDS / GM-MDS / reduced-intersection-matrices — the fleet's active GM-MDS lane,
`higher-order-mds-formalization-blueprint.md`, `LovettThm17Reduction.lean`)? The structured domain is
exactly the non-generic case the BGM machinery does NOT cover. These 3 are NEW to the catalog (verified
absent) and pin the explicit-vs-generic gap. None on disk; URLs for fetch.

| # | paper | id / venue | URL | why it bears on the open core |
|---|---|---|---|---|
| C1 | Berman–Shany–Tamo, **Explicit Subcodes of Reed–Solomon Codes that Efficiently Achieve List Decoding Capacity** (IEEE-IT 2025) | arXiv **2401.15034** | https://arxiv.org/abs/2401.15034 | EXPLICIT, no-randomness capacity via **orbits of two affine transformations with coprime orders** + tensor/cyclic-shift, length=field size, non-prime fields OK. Closest analogue to a structured-domain capacity result; its orbit/cyclic technique is a candidate for the smooth-subgroup μ_n case (though it is a folded subcode, not plain RS on μ_n — the gap). |
| C2 | **Randomly Punctured Reed–Solomon Codes Achieve List-Decoding Capacity over Linear-Sized Fields** (STOC 2024) | DOI **10.1145/3618260.3649634** (arXiv 2304.01403/2304.09445 versions on disk) | https://dl.acm.org/doi/10.1145/3618260.3649634 | The field-size-optimal BGM successor: capacity over `O(n)` fields. The prize regime has `q≈n·2^128 ≫ n`, so field size is NOT the obstruction — isolating that the obstruction is purely the *structured* (non-random) evaluation set. |
| C3 | **Near-Optimal List-Recovery of Linear Code Families** | arXiv **2502.13877** (2025) | https://arxiv.org/abs/2502.13877 | List-RECOVERY (the LD grand-challenge's multi-list generalization, the form correlated agreement feeds into); near-optimal bounds for linear-code families — check whether its machinery applies to the RS/subgroup case past Johnson. |

**Honest scope:** leads on the generic→explicit gap, NOT a closure. BGM-style results need the
evaluation points GENERIC (random / general position); the prize's smooth μ_n domain is maximally
structured (a subgroup), which is precisely why no published result reaches capacity for it. The
fleet's GM-MDS lane (Theorem 1.7 → one coordinate-merge residual) is the in-tree attack on this route.

## δ* halo-residual — the "house of Gaussian periods" thread (2026-06-13, distinct community)

The residual `max_c|η_c|` is exactly the **house (max conjugate modulus) of a Gaussian period**.
A SEPARATE research community (Duke–Garcia–et al., supercharacter theory + explicit norms/moments,
Hasse–Weil) studies precisely this object — distinct toolset from the Katz/Bourgain analytic thread
above. Verified via web search (Jun 2026); none on disk.

| # | paper | id | why it bears on the residual |
|---|---|---|---|
| G1 | **The Norm of Gaussian Periods** | arXiv **1611.07287** | Asymptotics of the logarithmic absolute NORM `Π_c η_c` (improves trivial bound) — the geometric-mean companion to the house `max_c|η_c|`; lower-bounds the house via `house ≥ |norm|^{1/m}`. |
| G2 | **Moments of Gaussian Periods and Modified Fermat Curves** | arXiv **2112.13886** | Computes the 4th absolute moment of Gaussian periods via **Hasse–Weil on Fermat curves** — EXACTLY the `E_2=3n²−3n` energy floor the in-tree `ShawFlatnessRefuted`/`SidonModNeg` use, from the curve side; the higher-moment generalisation is the prize's open `E_r`. Ties to the in-tree Hasse-multiplicity curve programme. |
| G3 | **The graphic nature of Gaussian periods** (Duke–Garcia–Lutz) | arXiv **1212.6825** | Foundational supercharacter framework + empirical house/value-distribution structure of `{η_c}`; the structural lens on why generic `μ_n` looks random (the genericity certificate). |

**Honest scope:** the Duke–Garcia norm/moment results are sharp for `n` a FIXED prime as `p→∞`
(opposite of the prize's growing dyadic `n=2^k`), so the same uniformity gap remains — but the
supercharacter + Hasse–Weil moment machinery is a genuinely different, formalizable handle on `E_r`
than the analytic Katz thread, and G2's curve method already underlies the in-tree 4th-moment floor.
The prize stays open; this widens the toolset on the named residual.

## δ* halo-residual — the Salem–Zygmund / generic-chaining route (2026-06-13, probability × NT)

NEW cross-field route (`docs/kb/deltastar-salem-zygmund-gausssum-chaining-2026-06-13.md`): the period
DFT identity `η_c=−1/m+(1/m)Σ_j τ(χ_j)e(−jc/m)` makes `max_c|η_c|` the SUP-NORM of the Gauss-sum
trigonometric polynomial. Prize ⟺ that sup-norm is Salem–Zygmund-generic `√(n log m)`; provable via a
sub-Gaussian MGF / generic-chaining bound (increment geometry only, NOT all moments). Papers (web,
Jun 2026; none on disk):

| # | paper | id | role in the route |
|---|---|---|---|
| SZ1 | Salem–Zygmund, **sup-norm of random trigonometric polynomials** (+ modern: Kahane *Some Random Series of Functions*) | classical | the `‖P‖_∞≍√(N log N)` law the Gauss-sum poly must match; the random model to derandomize. |
| SZ2 | Talagrand, **generic chaining / γ₂ bound on sub-Gaussian suprema** | *Upper and Lower Bounds for Stochastic Processes* (+ arXiv 1309.3522 tail-via-chaining, 2511.06338 L^q empirical process) | the apparatus: bounds `E max_c|η_c|` from increment metric `d(c,c')=‖η_c−η_{c'}‖_{ψ₂}` — needs only MGF/increment geometry, not every moment. The feasibility win. |
| SZ3 | **Equidistribution and independence of Gauss sums** | arXiv 2207.12439 (Adv. Math. 2024) | the derandomizer: joint independence of `{τ(χ_j)}` ⟹ the MGF factors ⟹ sub-Gaussian proxy `n`. Open part = uniformity over `m−1` chars. |
| SZ4 | Demirci Akarsu–Marklof, **value distribution of incomplete Gauss sums** | arXiv 1207.1607 | the limit law for exactly this sum class; gives the distributional shape (Gumbel tail) underpinning the SZ prediction. |
| SZ5 | Hegyvári, **On the distribution of additive energy revisited** | arXiv 2602.01781 (Feb 2026) | freshest on the `E_r` distribution (density + ratio lower bound of energy values) — the moment-side companion / refutation oracle for the SZ-genericity. |

**Honest scope:** this reframes the open core into a Salem–Zygmund/sub-Gaussian-MGF statement with a
mature toolkit (Deligne–Katz equidistribution + Talagrand chaining), strictly weaker than the raw
all-moments wall — but the quantitative joint Gauss-sum independence over `m−1≈p/n` characters at thin
`n≈p^{0.12}` remains open. A better-tooled route, not a closure. The prize stays open.

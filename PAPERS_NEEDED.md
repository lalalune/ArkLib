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

## Prize-regime sub-Johnson list-decoding reading list (issue #389/#371, 2026-06-13)

The deep-band MCA programme reduces (issue #389) to: bound the sub-Johnson
list size of EXPLICIT smooth-domain (dyadic μ_{2^μ}) Reed–Solomon codes.
Papers to obtain (none currently on disk — `~/papers/arklib/` is empty):

| # | Paper | Identifier | Why |
|---|---|---|---|
| P1 | Arnon–Boneh–Fenzi, *Open Problems in List Decoding and Correlated Agreement* | IACR ePrint 2026/680 | THE prize paper; grand MCA + grand list-decoding challenges, the regime |
| P2 | Ben-Sasson–Kopparty–Radhakrishnan, *Subspace Polynomials and List Decoding of RS* | FOCS 2006 / IEEE-IT 2010 | super-poly list just beyond Johnson on SUBSPACE eval sets — the additive analog of dyadic μ_{2^μ}; the explosion risk |
| P3 | Brakensiek–Gopi–Makam, *Generic RS codes achieve list-decoding capacity* | STOC 2023 / arXiv 2206.05256 | RANDOM eval points → capacity (small lists); contrast with structured/dyadic |
| P4 | Guruswami–Rudra, *Limits to List Decoding RS Codes* | IEEE-IT 2006 | list-size lower bounds; what structured RS can force |
| P5 | Kopparty–Ron-Zewi–Saraf–Wootters, *Improved decoding of folded RS & multiplicity codes* | FOCS 2018 / arXiv 1805.01498 | capacity-achieving via folding = a multiplicative/Frobenius structure close to μ_n |

Also re-check in-tree: ECCC TR25-169 (barrier), ePrint 2026/861 (action-orbit),
2026/858 (threshold-halving) — listed above, may bear on the dyadic explosion.

## Prize positive-direction adds (2026-06-13, Johnson-scale fiber collapse)
| # | Paper | Identifier | Why |
|---|---|---|---|
| P6 | Mann, *On linear relations between roots of unity* | Mathematika 12 (1965) 107–117 | minimal vanishing sums of roots of unity = rotated subgroups; governs the Johnson-scale esymm-fiber collapse |
| P7 | Conway–Jones, *Trigonometric Diophantine equations* | Acta Arith. 30 (1976) 229–240 | structure of vanishing sums of roots of unity (the e_1=0 fiber) |

## Prize analytic-core adds (2026-06-13, the subgroup-Gauss-sum moment wall)
| # | Paper | Identifier | Why |
|---|---|---|---|
| P8 | Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups* | Annals of Math Studies 116 (1988) | Sato–Tate / equidistribution & moments of (subgroup) Gauss sums via sheaf monodromy — the deviation in clean-moments |
| P9 | Shkredov, *On the additive energy of the multiplicative subgroup* (and sequels) | arXiv 1212.xxxx / Izv. Math | higher additive energy `E_r(μ_n)` bounds for multiplicative subgroups of `F_p` — the equivalent sum-product form of the wall |
| P10 | Bourgain–Garaev, *Sum-product estimates and exponential sums over subgroups* | J. reine angew. Math (2014) | exponential sums / additive energy over subgroups in the `n ~ p^{1/β}` (constant-rate) regime |
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

## δ* — the Lamzouri value-distribution CLT edge (2026-06-13, decisive localization)
The prize ⟺ extending the Gaussian value-distribution CLT past its proven `log H=o(log q)` range to
fixed-power length `n=p^β`. See `deltastar-salem-zygmund-gausssum-chaining-2026-06-13.md` §"DECISIVE".
- Lamzouri, **The distribution of short character sums**, arXiv **1106.6072** (Camb. Phil. Soc.) — 2-D
  Gaussian limit for `log H=o(log q)`, quantitative Kolmogorov rate; the proven positive direction.
  Prize regime `n=p^{1/8}` is exactly where it stops. THE paper for the residual.
- Lamzouri–Mangerel, **Large odd order character sums & improvements of Pólya–Vinogradov**, arXiv
  **1701.01042** — max partial sum `M(χ)≪√q(log q)^{1−δ_g}` (fixed order); the max-side analogue.
## ExcessCensusLaw analytic core (general-r deep-band #bad-scalar / e1-e2 joint level-set — #389 demand-side lane)
The r=3 deep-band #bad-scalar bound is CLOSED in-tree (`DeepBandR3Bound.lean`, O172 closed form #bad = n*C(n/4,2)+1 <= K, axiom-clean). The remaining obligation past r=3 — the general-r deep-band #bad count, equivalently the magnitude of the (e1,e2)-joint level-set / m-th moment subset-sum count over a multiplicative subgroup (the ExcessCensusLaw analytic core) — is OPEN and blocked on exactly these papers. Each plugs into a NAMED in-tree object. Drop location ~/papers/arklib/ (worktree copy empty — all rows fetch-needed).
- arXiv:1910.05894 — Lai–Marino–Robinson–Wan, "Moment subset sums over finite fields", FFA 62 (2020) 101607. HIGHEST PRIORITY: the e1-e2 joint-level-set = k-MSS(2) paper (matches O22 `twoSymmetric_count_eq_e1_psum2_count` via Newton). Supplies the subgroup-restricted partial Gauss-sum bound (Cor 1: <=(mn+1)√q — the open `subgroup_quadratic_sum_is_partial` input) + Li–Wan sieve. OPEN ACCESS: PMC PDF https://pmc.ncbi.nlm.nih.gov/articles/PMC10941333/ ; NIST/CSRC final.
- arXiv:2401.06964 — Gottig–Pérez–Privitelli, "An approach to the moments subset sum problem through systems of diagonal equations over finite fields" (2024). The diagonal-system F_q-point-count route to the joint count (= ExcessCensusLaw analytic core / N2=collisionCount magnitude). OPEN ACCESS (use arxiv.org/html/ or /pdf/ — abs page blocked in env).
- arXiv:2008.11268 — Christie–Dykema–Klep, "Classifying minimal vanishing sums of roots of unity" (2025 rev). Cyclotomic vanishing-sum spectrum to weight 21 (extends Poonen–Rubinstein wt-12); governs which deep-band bad configs exist at general r (in-tree `LamLeungTwoPow.vanishing_iff_antipodal_coeffs`). OPEN ACCESS (www.arxiv.org/abs/ mirror).
- arXiv:2202.07555 — Łaba–Marshall, "Vanishing sums of roots of unity and the Favard length of self-similar product sets", Discrete Analysis 2022:21. Sharpens the Lam–Leung weight floor — caps how low-weight (deep, deficit-2) a vanishing relation can be, bounding general-r list size. OPEN ACCESS: discreteanalysisjournal.com/article/57602 ; UBC preprint Favard-two-primes.pdf.
- Hanson (–Petridis), "Refined estimates concerning sumsets contained in the roots of unity", Proc. LMS 122 (2021). PAYWALLED (Wiley plms.12322 — REQUEST). The F_q additive-energy quantity that would bound M2=collisionCount (pairs with in-tree `AdditiveEnergyResultant.lean`, `EnergyInjection.lean`); O30's `SubgroupRepCountFiniteFieldCounterexample` shows the char-0 energy bound FAILS over F_q, so this is the true obstruction.
- math/9605216 — Lenstra et al., "Vanishing sums of m-th roots of unity in finite fields" (SLMath 1996-028). REQUEST text PDF (Leiden copy is image-only scan). The char-0 <-> char-p weight-set W_p(m) transfer behind the O172 q-threshold ("production q = saturating-envelope worst case") + per-prime falsifier surplus (+11/+54 spurious mod-p solutions). Companion: Lam–Leung, J. Algebra 224 (2000) 91-109 (char-0 weight set; backbone of in-tree `LamLeungTwoPow`).
- arXiv:2409.13515, arXiv:2502.14436 — incomplete/sparse multiplicative character sums over subgroups (2024-25; latter improves Mérai–Shparlinski–Winterhof for 0.13<ρ<0.32). Sharpest current subgroup partial-char-sum bounds in the prize ρ-window — the missing `subgroup_quadratic_sum_is_partial` analytic input (in-tree `ConcreteWeilInstance.lean`, `SubgroupGaussSumAntiConc.lean`). OPEN ACCESS.
- Supporting (additive energy of multiplicative subgroups, OPEN): Alon–Bourgain "Additive patterns in multiplicative subgroups" (princeton multip3.pdf); Shkredov/Murphy–Petridis arXiv:1102.1172, arXiv:1303.2729.
- NOTE for fetcher: arxiv.org abs pages BLOCKED for WebFetch in this env; arxiv.org/html/<id>, arxiv.org/pdf/<id>, www.arxiv.org/abs/<id>, PMC and university PDFs fetch fine.

## δ* — the Favard-length / self-similar NON-MOMENT route (2026-06-13, harmonic analysis × NT)
The impossibility map forces a non-moment method; this is the first that fits the dyadic tower. See
`docs/kb/deltastar-favard-length-selfsimilar-route-2026-06-13.md`. Papers:
- Łaba–Marshall, **Vanishing sums of roots of unity & Favard length of self-similar product sets**,
  arXiv **2202.07555** (Discrete Anal. 2022) — improves Lam–Leung; non-moment sup/L¹ decay via
  vanishing-sum structure; built for self-similar iterated products = the 2-power tower μ_{2^k}.
- Nazarov–Peres–Volberg, **Favard length of the 4-corner Cantor set ≤ n^{−c}** (Ann. Math. 2010) +
  Bond–Łaba–Volberg — the method's origin.
- **On vanishing sums of m-th roots of unity in finite fields**, arXiv **math/9605216** — the char-p
  engine governing the halo excess.
- Poonen–Rubinstein / arXiv **2008.11268** classifying minimal vanishing sums — the input bound.
ALSO (crypto-side, confirms NOT above Johnson — do NOT chase as a lever): Haböck **eprint 2025/2110**
(MCA = ordinary CA up to Johnson via Guruswami–Sudan), **2025/2051** (all-poly-generators MCA).

## δ* OPEN-CORE reading list addendum — 2026-06-13c (state-of-the-art subgroup-sum bounds; the BGK→Burgess gap)

Independent literature re-confirmation (fleet already has the state-of-the-art Di Benedetto bound in
`deltastar-literature-findings-2026-06-13.md`). The prize core `max_c|Σ_{x∈μ_n}e_p(cx)| ≤ n^{1/2+o(1)}`
at `n~p^{1/4}` is OPEN; the best PUBLISHED bound is the BGK-family power-saving:
- **Di Benedetto–Garaev–García–González-Sánchez–Shparlinski–Trujillo (2020, arXiv 2003.06165)**:
  `n^{1−31/2880+o(1)}` for `n>p^{1/4}` — `δ≈0.0108`, vs the prize-needed `δ=1/2`. This is the SOTA and
  the precise distance to the prize: ~45× in the power-saving exponent. No √-cancellation exists.
3 papers NEW to catalog (on-topic additive-combinatorics/char-sum; NONE a √-cancellation breakthrough):

| # | paper | id | URL | bearing on the core |
|---|---|---|---|---|
| S1 | **Restricted sumsets in multiplicative subgroups** | arXiv **2309.10950** | https://arxiv.org/abs/2309.10950 | restricted/structured sumsets inside μ_n — the additive structure governing the energy/excess; check vs the antipodal/Lam-Leung characterization. |
| S2 | **Structure theory of set addition with two operations** (2026) | arXiv **2601.12457** | https://arxiv.org/abs/2601.12457 | sum-product / two-operation structure — the engine class behind BGK; whether its newest form sharpens the subgroup power-saving. |
| S3 | **Mixed character sums modulo prime powers** (2026) | arXiv **2604.02614** | https://arxiv.org/abs/2604.02614 | mixed (additive×multiplicative) char sums; prize is mod prime but the amplification technique may transfer to the subgroup case. |

**Honest scope:** these are leads on the BGK→Burgess gap, NOT a closure. The published SOTA
(`n^{1−1/2880}`) confirms the prize's `n^{1/2}` cancellation is a recognized open problem with no
current solution; every moment-method route is ruled out (`deltastar-moment-method-convergence-diagnosis`),
and the only non-moment hope is a Stepanov/Burgess amplification that does not yet exist.

## 2026-06-13 (c) — polynomial-method / subgroup-energy papers (the slice-rank lane check)
- arXiv:1712.00410 — Murphy-Rudnev-Shkredov-Shteinikov, few-products-many-sums. RECORD subgroup energy E<~|A|^{2.45}; incidence+sum-product (NOT slice rank). The current wall.
- arXiv:1102.1172 — Heath-Brown-Konyagin, additive shifts of multiplicative subgroups. Stepanov: E<<|A|^{5/2}, |A|<<p^{2/3}. The Stepanov ceiling.
- arXiv:1905.07355 — Costa-Dalai, gap in slice rank of k-tensors. Slice rank fails for >=8-term systems; energy is in the weak regime.
- arXiv:2304.13801 / 2309.09124 — Hanson-Petridis, additive decompositions / multiplicative structure of shifted subgroups. Most-adaptable Stepanov refinement; still cannot break the degree-vs-multiplicity balance.
- Slice-rank survey (Surveys in Combinatorics 2024, Cambridge) — confirms slice rank is an avoidance-size method needing F_q^n; no subgroup-energy application exists.
## δ* EFFECTIVE-EQUIDISTRIBUTION cluster — 2026-06-14 (the FIXED-INDEX wall, NOT thin-BGK)

Added by the regime-clarification lane (probe `probe_fixed_index_supnorm_ratio.py`). **Key
reframing:** the prize fixes `q≈n·2^128`, i.e. index `m=(q−1)/n≈2^128` HELD CONSTANT as the
FFT domain `n→∞`. This is a *fixed-index, positive-proportion* (`n=Θ(p)`) subgroup family — the
`β∈[4,5]` figure is the *derived* `β=1+128/log₂n`, NOT a fixed thin-subgroup exponent. So the
analytic wall is **effective Gauss-sum equidistribution** (the `m` fixed Gauss-sum phases must
avoid alignment at the specific `p≈2^160`), geometrically distinct from additive-combinatorial
BGK/Paley (thin `n=p^{δ}`, `δ<1`). All 5 ON DISK at `~/papers/arklib/`.

| # | paper | id | why it bears on the FIXED-INDEX wall |
|---|---|---|---|
| EQ1 | Perret-Gentil (et al.), **Wasserstein metrics and quantitative equidistribution of exponential sums over finite fields** | arXiv **2505.22059** (2025) | THE effective version of Deligne/Katz equidistribution. Gives `W₁`-discrepancy of trace-function families via Weyl sums — `√p`-quality (conductor/`√p`). **Confirms the no-go:** this quality is `≫ 1/m` needed to certify flatness of `m=2^128` phases at `p≈2^160`, so effective-Katz alone cannot close the prize (but is the right machine for the fixed-index framing). |
| EQ2 | Rojas-León, **Equidistribution and independence of Gauss sums** | arXiv **2207.12439** | Proves joint independence/equidistribution of Gauss sums for `n` monomials in `r`-variable mult. characters — the QUALITATIVE (q→∞) non-conspiracy of exactly our phases `τ(ψ^j)/√p`. The prize is its EFFECTIVE form. |
| EQ3 | **On an uncertainty principle for small index subgroups of finite fields** | arXiv **2310.09992** | ★ DECISIVE BRIDGE. The **nonvanishing-minors (NVM) property of the compressed Fourier matrix of a subgroup H** = the higher-order-MDS / repeated-degree generalized-Vandermonde nonsingularity that **R3 `LovettPrimitiveStep` needs** — and it is characterized **via Gauss sums** (Chebotarëv on roots of unity). Solves index 2,3; **"larger index remains open"** (quote). So R3 (algebraic) and the analytic Gauss-period sup-norm are the **SAME open object**; the campaign's "independent routes" collapse. |
| EQ4 | **Improved bounds on Gauss sums in arbitrary finite fields** | arXiv **1712.00761** | SOTA effective single Gauss-sum / subgroup-sum bounds in `F_q`; the quantitative input feeding both walls. |
| EQ5 | Perret-Gentil, **Ultra-short sums of trace functions** | arXiv **2302.13670** | Equidistribution of *very short* trace-function sums over zeros of integral polynomials — the short-interval analogue of the incomplete `S(t)=Σ_{x∈μ_n}e_p(tx)` sup-norm tail. |

**Honest scope:** the fixed-index reframing moves the prize OFF the (hopeless) thin-BGK wall onto
the effective-equidistribution wall — but `probe_fixed_index_supnorm_ratio.py` + the conductor
estimate (EQ1) show BOTH walls, and the moment/Betti route, give only **poly(m)·p^{−1/2}** quality
while certifying no-alignment of `m≈2^128` phases needs **`≤1/m`** quality. The wall is therefore
*framing-independent* (triangulated 3 ways), and remains open. New empirical law (the one clean
positive): `R(n,m) := M/√(n·ln m)` is FLAT ≈ 1.1–1.5 across `n:16→2048` and index `m:13→8206`
(thinning to `n=p^{1/2.63}`) — so the `log(p/n)` factor in `δ*=1−ρ−H(ρ)/(β log₂n)` is the EXACT
normalization, worst-case constant `C≈1.5`, not merely an upper bound.

## 2026-06-13 (d) — 5 new papers on the EXACT prize core (incomplete additive char sum over μ_n)

The #407 core localizes to `M(n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)| ≤ n^{1/2+o(1)}` at `n ~ p^{1/4}`
(the additive character over a small multiplicative subgroup — the Gauss-sum-like object, distinct
from the multiplicative-char sums already cataloged). SOTA = BGK power-saving `n^{1-1/2880}`
(Di Benedetto et al, 2003.06165). 5 leads, 2 downloaded to `~/papers/arklib/`:

| # | paper | id / source | status | bearing on the core |
|---|---|---|---|---|
| E1 | **Exponential sums over small subgroups, revisited** (2024) | arXiv **2401.04756** | DOWNLOADED | THE exact object — revisits BGK-type bounds for `Σ e_p(bx)`, `x∈μ_n` small; the current best-technique reference for the prize core. |
| E2 | **Bounds on exponential sums over small multiplicative subgroups** (Bourgain–Chang) | arXiv **0705.4573** | needs DL | the original small-subgroup additive-character cancellation; foundation for the `n^{1/2}` target and where the power-saving started. |
| E3 | **Multiplicative Energy of Shifted Subgroups and Bounds on Exponential Sums with Trinomials** | Canad. J. Math (Cambridge) | needs DL | shifted-subgroup energy + **trinomial** exp sums — the trinomial is precisely the monomial-far-line direction `X^b+γX^a`; the energy route in the live regime. |
| E4 | **Multiplicative character sums over subsets of quadratic extensions** (2025) | arXiv **2502.14436** | DOWNLOADED | recent char-sum machinery over structured subsets of `F_{p^2}` — technique transfer to the subgroup case. |
| E5 | **Shparlinski — Open Problems on Exponential and Character Sums** | web.maths.unsw.edu.au/~igorshparlinski/CharSumProjects.pdf | reference | the canonical open-problem list; confirms the prize core is recognized-open and names the adjacent attackable sub-problems (Burgess/Stepanov amplification — the only non-moment hope). |

**Honest scope (unchanged):** none of these is a `n^{1/2}` √-cancellation breakthrough; the published
SOTA `n^{1-1/2880}` and Shparlinski's problem list both confirm the prize core is a recognized open
problem in analytic number theory. Moment methods are exhausted (energy ≤ `n^{2+o(1)}`, the 7/3
barrier). E1+E3 are the most relevant — the revisited-small-subgroup technique and the trinomial
(= monomial-line) energy bound, in the live `n~p^{1/4}` regime.
## Proximity-prize reduced-form: the EXACT Gauss-sum-sup-norm / resonance face (added 2026-06-13b)

The δ* conjecture `max_b|η_b(μ_n)| ≤ √2·√(n log(q/n))` reduces to **resonance-freeness of the Gauss-sum
phases {τ(χ)}** (no `b` aligns Ω(f) of them) = the large-values/sup-norm problem for `∑_χ χ̄(b)τ(χ)`.
Targeted research (this session) — this input is NEITHER proven NOR resonance-refutable:

8.  arXiv:1604.01007 "On period polynomials of degree 2^m for finite fields" — the DYADIC period
    polynomials; explicit factorizations for `p≡3,5 (mod 8)`, but NOT root-magnitude (sup-norm) bounds
    in the `n~q^{1/4}` regime. Closest structural match; check if its 2-adic factorization constrains
    the max real period.
9.  Bondarenko–Seip, "The resonance method for large character sums", Mathematika — resonance LOWER
    bounds `√N·exp(c√(log N/log log N))` for multiplicative character sums over intervals. Refutation
    direction. Does NOT transfer to `∑_χ χ̄(b)τ(χ)` (rigid orthogonal dual-group sum, not a
    multiplicative interval sum; combination law contractive) — consistent with measured `C→√2`, no
    resonance blow-up. So the conjecture is NOT resonance-refutable.
10. arXiv:1712.00761 "Improved bounds on Gauss sums in arbitrary finite fields" — upper bounds for
    `∑χ(x^n)` up to order `q^{1/2+1/68}`; power-saving, not the sup-norm √-cancellation.
11. arXiv:1207.1607 Demirci Akarsu–Marklof "The value distribution of incomplete Gauss sums" — limit
    law for QUADRATIC incomplete Gauss sums (interval-restricted); different object (quadratic phase),
    but the "incomplete sum has richer value distribution than the complete √q-normalized one" theme is
    the same flavor as the subgroup sup-norm.
12. arXiv:2406.01519 (2024) — flagged by search under resonance/large-character-sums; obtain & check.

VERDICT (this session): the prize's open input (Gauss-sum resonance-freeness / sup-norm `≤√(n log)`) is
at the genuine research frontier — no proven bound reaches it, and resonance does not refute it. Cannot
be closed by citation; not fabricated.

## 2026-06-14 (#407): literature sweep — SOTA on both prize faces, confirms the gap is the open core
The prize δ* = where the worst far-line list crosses budget n. Two equivalent faces, both with SOTA
FAR from the prize target — confirming the core is open (the gap itself):
| # | Paper | Identifier | Bearing |
|---|---|---|---|
| L1 | Di Benedetto–Garaev–García–González-Sánchez–Shparlinski–Trujillo, *New estimates for exp sums over mult subgroups* | arXiv 2003.06165 | **SOTA char-sum face**: `max_a|Σ_{x∈H}e_p(ax)| ≤ |H|^{1−31/2880+o(1)}` for `|H|>p^{1/4}` — improves BGK, but is `n^{1−o(1)}`, FAR from prize `√(n log(q/n))=n^{1/2+o(1)}`. The gap IS the open core. |
| L2 | Shangguan–Tamo, *Combinatorial list-decoding of RS beyond the Johnson radius* | arXiv 1911.01502 | beyond-Johnson list size, but GENERIC/intersection-based, not dyadic μ_n worst case |
| L3 | Goldberg–Shangguan–Tamo (Ferber–Kwan–Sauermann line), *List-decodability with large radius for RS* | arXiv 2012.10584 | RS list-decodable to `1−ε`, rate `Ω(ε)` — but RANDOM/punctured eval points, `q≥n^{1+δ}`, NOT structured dyadic |
| L4 | *List-decoding & list-recovery of RS beyond Johnson for any rate* | arXiv 2105.14754 | any-rate beyond-Johnson, again generic eval sets, not the prize's fixed μ_n |
| L5 | *Weil sums over small subgroups* | arXiv 2211.07739 | Weil-type bounds for subgroup sums; complements the char-sum face |
VERDICT: the SOTA char-sum bound (Di Benedetto `n^{1−31/2880}`) and the beyond-Johnson RS list bounds
(random points) both MISS the dyadic prize regime by a polynomial factor. The prize = closing exactly
that gap = the recognized open grand list-decoding / Gauss-sum-sup-norm challenge. No 2024–2026 paper
closes the structured dyadic case. Confirms (literature-grounded) the open core every campaign framing
converges to.

## 2026-06-13 (#407): second sweep — the Paley-spectrum + char-p Lam–Leung faces (the char-p transfer wall)
The char-0 optimality is now axiom-clean Lean (`full_tower` etc.); the SOLE residual is the **char-p
transfer** (does a short gap-vanishing config of `2^μ`-th roots over `F_q` lift to a char-0 coset-union).
This sweep maps the two literatures that bound that exact object. NONE reach the prize scale.
| # | Paper | Identifier | Bearing |
|---|---|---|---|
| P1 | Podestá–Videla, *The nature of the spectrum of generalized Paley graphs and weak Waring numbers* | arXiv 2604.06513 (Apr 2026) | freshest; spectrum of `Cay(F_q,μ_k)` = Gaussian periods = the `η_b`. **STRUCTURAL ONLY** (when real/integral, period ≥3) — confirms NO new eigenvalue-MAGNITUDE bound exists for thin subgroups. |
| P2 | Podestá–Videla, *Spectral properties of generalized Paley graphs* | arXiv 2310.15378 | explicit Gauss-period spectra for index `k≤4`, `k=5` — the eigenvalues ARE the open-core periods; no thin-`n~q^{1/4}` magnitude bound. |
| P3 | Lam–Leung, *On vanishing sums of roots of unity* (+ char-p `W_p(m)` extension, arXiv math/9605216) | — | the char-p transfer = `W_p(2^μ)=ℕp+2ℕ`: gives weight-PARITY of a vanishing sum (`w<p ⟹ w even`) but NOT coset structure; the only general lift = norm bound `w^{φ(m)}<p`, unreachable at prize scale. |
| P4 | *Note on vanishing power sums of roots of unity* | arXiv 1503.07281 | simultaneous power-sum vanishing structure (our gap window is many `p_j=0` at once — the one place a poly-height argument could live). |
| P5 | Alsetri, *Burgess-type character sum estimates over generalized arithmetic progressions of rank 2* | arXiv 2509.07765 (BLMS 2026) | closest recent TECHNIQUE (mult-energy + Bohr-set/geometry-of-numbers à la Konyagin) but rank-2 GAP ≠ mult subgroup; does not transfer to `μ_n`. |
| P6 | Kambiré, *Proximity Gaps Conjecture Fails Near Capacity over Prime Fields* | arXiv 2604.09724 / eprint 2026/782 | the construction paper itself (the δ* lower bracket = monomial line `X^{rm}+λX^{(r−1)m}`, `λ∈H^{(+r)}`). |
VERDICT: the two literatures that bound the char-p transfer object (Paley spectrum = Gauss periods;
char-p Lam–Leung weight sets) are STRUCTURAL — neither gives a magnitude/lift bound reaching the prize
`q=n^β` for `n~q^{1/4}`. Confirms the residual is the recognized open core, not a literature lookup.

## 2026-06-13 (#407): CURRENT open-problem status of the reduced core (Paley graph conjecture)
The prize floor = BCHKS Conj 1.12 = Paley-graph-conjecture territory. Most up-to-date literature status:
| # | Paper | Identifier | Bearing |
|---|---|---|---|
| Q1 | *Randomstrasse101: Open Problems of 2025* | arXiv 2603.29571 (31 Mar 2026) | **DECISIVE**: curated random-structures open-problem list, dated 3 months ago, STILL lists the Paley-graph clique number `ω(G_p)=O(polylog p)?` as OPEN. The reduced core is open in the current literature, full stop. |
| Q2 | Hanson–Petridis, *clique number of the Paley graph* (via Stepanov/polynomial method) | — | best PROVEN upper bound `ω(G_p) ≤ (1+o(1))√(p/2)` — the `√p` barrier, FAR from `polylog`/`√(n log q)`. The bound the prize needs to beat is exactly here, and it hasn't moved. |
VERDICT (current as of Jun 2026): the object the prize floor reduces to is on the March-2026 official
open-problems list. There is no known-math closure. A prize solution "reducing to proven math" must
supply a NEW sub-`√p` thin-subgroup character-sum / Paley bound that the 2026 open-problems list says
does not yet exist. (The "Paley graph conjecture on double character sums implies many character-sum
estimates" — it is the governing open conjecture, not a side lemma.)

## δ* — the "does smoothness beat BGK?" check (2026-06-14, NO-LEVER confirmed)

Tested whether the prize subgroup's 2-power/smooth order gives better-than-generic-BGK
cancellation for the sup bound. **Answer: NO** (size-governed, not smoothness-governed). 3 papers
on disk `~/papers/arklib/`.

| # | paper | id | finding |
|---|---|---|---|
| SC1 | Bourgain–Chang, **Bounds on exponential sums over small multiplicative subgroups** | arXiv **0705.4573** | Thm 1.1: `\|H\|>p^α ⟹ \|Σ_{x∈H}e_p(x)\| < \|H\|·p^{−β(α)}`, `β=β(α)` via sum-product. The saving depends ONLY on the SIZE ratio `α=log\|H\|/log p` — **no smoothness/factorization dependence**. So the prize's 2-power order does NOT improve the analytic sup exponent; smoothness only feeds the moment/energy side (which caps at the Betti wall). Confirms the sup bound is the genuine size-governed BGK wall. |
| SC2 | **A supercharacter approach to Heilbronn sums** | arXiv **1312.1034** | Supercharacter/Gaussian-period toolset (Duke–Garcia–Lutz lineage) for subgroup sums; the structural (not exponent-improving) lens on `μ_n` periods. |
| SC3 | **Supercharacters, exponential sums, and the uncertainty principle** | arXiv **1208.5271** | Supercharacter uncertainty principle = the NVM/compressed-Fourier face (ties to 2310.09992 / R3 NVM). |

**Honest finding:** the analytic sup bound `M ≤ C√(n log m)` is the BGK size-wall, NOT improvable by
the 2-power smoothness. The smoothness is genuinely useful ONLY on the char-0 moment scaffold
(Lam–Leung antipodal, `E_r ≤ (2r−1)‼·n^r`), which provably caps at the Betti depth `r=2` and cannot
reach the sup. So the two faces are decoupled: smoothness helps the (capped) moment side, the sup
side is size-governed and open. No smoothness lever exists for the prize.

## 2026-06-14 (e): the reduced object = additive energy of multiplicative subgroups

Face 3 reduces EXACTLY to `E_+(μ_n) ≤ n^{2+o(1)}` (equiv. `max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤
n^{1/2+o(1)}`), open: best proven HBK `n^{5/2}` (`n<p^{2/3}`), BGK `n^{1-ε}` power-saving. The
antipodal reduction (this session) restates it as: count short bounded-coeff polynomials
`D(X)` (`deg<n/2`, `Σ|coeff|≤2r`) with `D(g)≡0 mod p`. 5 papers on this exact object:

- **F1** arXiv:2602.01781 "On the distribution of additive energy revisited" (2026) — Fourier +
  random-structure analysis of multiplicative-energy distribution; small-doubling covering
  estimate. NOT a sub-HBK subgroup bound, but the distributional angle may bound the bad-prime
  tail (the sparse exceptional set my probes found). DOWNLOAD.
- **F2** Kim–Yip–Yoo "Multiplicative structure of shifted multiplicative subgroups and its
  applications to Diophantine tuples", Canad. J. Math (2025) — shifted-subgroup multiplicative
  structure; the shift `λ` is the far-line direction. DOWNLOAD (Cambridge Core).
- **F3** arXiv:2103.09438 "Gauss sums and the maximum cliques in generalized Paley graphs of
  square order" — direct Paley-eigenvalue/Gauss-sum link (face-3 graph). DOWNLOAD.
- **F4** arXiv:2603.24788 "Algebraic Expander Codes" (2026) — algebraic expansion + codes; may
  give a code-side route to list size avoiding the worst-case energy. DOWNLOAD.
- **F5** Alon–Bourgain "Additive Patterns in Multiplicative Subgroups"
  (web.math.princeton.edu/~nalon/PDFS/multip3.pdf) — additive structure forced/forbidden in
  subgroups; directly bounds short additive relations = my short-poly count. DOWNLOAD.

## #407 char-p transfer / trinomial-energy sweep (2026-06-14, wakesync)
- [LL96fin] Lam, Leung — Vanishing Sums of m-th Roots of Unity in Finite Fields (arXiv math/9605216; J. Algebra). EXACT char-p transfer citation: W_p(2^μ) ⊇ ℕp+2ℕ ⟹ new relation needs weight≥p ⟹ norm exponent φ(n)=n/2 wall. PRIORITY.
- [MSS18] Macourt, Shkredov, Shparlinski — Multiplicative Energy of Shifted Subgroups & Bounds on Exponential Sums with Trinomials in Finite Fields (Canad. J. Math. 70(6), 2018). Trinomial incidence = far-line object; candidate q-uniform energy route. PRIORITY.
- [Bur-GAP25] Burgess-type character sum estimates over generalized arithmetic progressions of rank 2 (arXiv 2509.07765, Sep 2025). {0..k-1,a,b} = rank-2 GAP; candidate direct I(δ) bound.
- [BG-small24] Exponential sums over small subgroups, revisited (arXiv 2401.04756, 2024). Best explicit small-subgroup BGK exponents.
- [Shp-open] Shparlinski — Open Problems on Exponential and Character Sums (web.maths.unsw.edu.au/~igorshparlinski/CharSumProjects.pdf). Confirms explicit BGK is OPEN.

## 2026-06-14 (f): recent LD-capacity breakthroughs + improved subgroup Gauss sums — why they MISS the prize

The 2022-2024 RS-list-decoding-capacity results all certify capacity via **higher-order MDS /
MDS(ℓ) / GM-MDS genericity**, which the smooth-domain prize code `μ_n` PROVABLY LACKS
(`HigherOrderMDSOrderThreeFail.lean`; `MuTwoPowDerandRefutation.lean:272` "capacity machinery
fails on μ_8"). So they do NOT transfer to the explicit `s=1` smooth prize — both grand
challenges (MCA + LD) collapse to the SAME obstruction: explicit smooth structure where
genericity fails ⟹ the subgroup character-sum bound. 5 papers:

- **G1** arXiv:2206.05256 Brakensiek–Gopi–Makam "Generic Reed–Solomon Codes Achieve List-decoding
  Capacity" — resolves Shangguan–Tamo; the MDS(ℓ) route. The prize is the NON-generic case it
  excludes. DOWNLOAD.
- **G2** arXiv:2304.09445 "Random RS Codes Achieve List-Decoding Capacity, Linear-Sized Alphabets".
- **G3** arXiv:2304.01403 "Randomly Punctured RS Codes Achieve LD Capacity, Poly-Size Alphabets" —
  the prize's `μ_n` is EXPLICIT not randomly-punctured (the gap). DOWNLOAD.
- **G4** arXiv:2401.15034 "Explicit Subcodes of RS that Efficiently Achieve LD Capacity" — closest
  to explicit; check whether its construction is smooth-domain-compatible or needs subcoding the
  prize forbids. DOWNLOAD.
- **G5** arXiv:1712.00761 "Improved bounds on Gauss sums in arbitrary finite fields" — subgroup
  Gauss sums to `q^{1/2+1/68}` (improves Zhelezov); directly the MCA object, small power-saving
  above √q. DOWNLOAD.

## 2026-06-14 (g): continuation web scan — newest adjacent hits, no closure

Fresh web scan for 2025-2026 papers around Gaussian periods, generalized Paley graphs, subgroup
character sums, and RS list decoding.  These are either already cataloged above or newly noted here;
none supplies the missing `M(μ_n) ≤ √(n log m)` / centered deep-moment estimate.

- arXiv:2604.06513, Podestá–Videla, "The nature of the spectrum of generalized Paley graphs and
  weak Waring numbers over finite fields" — already cataloged as P1; structural Gaussian-period
  spectrum, no new magnitude bound.
- arXiv:2603.03841, Kumar–Ron-Zewi, "Advances in List Decoding of Polynomial Codes" — already
  cataloged; capacity progress routes through generic/MDS-style structure, not the fixed smooth
  multiplicative subgroup.
- arXiv:2602.22167, "Estimates for Character Sums in Finite Fields, F_p^n" — extension-field /
  polynomial-argument character-sum estimates; adjacent technique only, not an additive-character
  sup-norm bound over `μ_n ⊂ F_p`.
- arXiv:2511.18304, "The automorphism groups and identification of some Generalized Paley graphs" —
  graph structure/isomorphism side of generalized Paley graphs; confirms relevance of the Paley
  object but does not bound Gaussian-period eigenvalue magnitudes.
- arXiv:2502.14436, Cheng–Winterhof, "New estimates for character sums over sparse elements of
  finite fields" — already cataloged; multiplicative-character/sparse-set estimates, not the
  required additive-character subgroup period bound.

## 2026-06-14 — fresh lit sweep against the REDUCED forms (max Gauss period = Paley λ₂ = additive energy = subset-sum)

Searched for any 2025/2026 work moving the prize's reduced forms. **Conclusion: landscape unchanged;
no paper breaks the BGK/5-2 wall at the prize point.** Logged for the record (all open-access; download
if doing the BGK lane):
- **arXiv:2602.22167**, Chattopadhyay, "Burgess-Type Bounds for Character Sums over F_{p^n}" (Apr 2026) —
  genuinely 2026, but EXTENSION fields F_{p^n} / boxes, not the prime-field thin multiplicative subgroup;
  does not bound the max incomplete Gauss sum over μ_n ⊂ F_p. Not applicable.
- **arXiv:1706.05651**, "Incomplete Gauss sums modulo primes" (Vinogradov method) — incomplete sums over
  INTERVALS, power-saving not √n; wrong truncation (interval, not subgroup).
- **arXiv:1207.1607**, "The value distribution of incomplete Gauss sums" — a limit LAW for interval-
  truncated Gauss sums (distributional), not a worst-case sup-norm over a subgroup.
- **"Refined estimates concerning sumsets contained in the roots of unity"** (ResearchGate 341796922) —
  the additive/subset-sum structure of roots of unity = the BCHKS Conj 1.12 reduced form; same Lam–Leung
  vanishing-sums machinery already in-tree; no new 2-power-subgroup count bound that helps.
- **arXiv:1303.2729**, "A note on sumsets of subgroups in Z_p*" — the Stepanov-method `E(A) ≪ |A|^{5/2}`
  for `|A| ≪ p^{2/3}` (the 5/2 energy barrier). Confirms the energy route is √-lossy for δ* (FATAL).
- **Alon–Bourgain, "Additive Patterns in Multiplicative Subgroups"** — vanishing sums of roots of unity
  (Lam–Leung) for additive-equation-free subgroups; same machinery, no sup-norm.
- **arXiv:2603.29571**, "Randomstrasse101: Open Problems of 2025" — open-problems collection; check whether
  it lists the thin-subgroup Gauss-period sup / Paley-eigenvalue status (likely confirms OPEN).

NET: the reduced forms confirm the in-tree map — best energy `|A|^{5/2}` (√-lossy), best sup BGK `n^{1-o(1)}`
(di Benedetto `n^{0.989}`), Ramanujan only semiprimitive (not prize point). No citable closure exists.

## §5.0 Mahler-measure / flat-Littlewood lens — 2026-06-14 (KILLS the "structure-aware norm bound" route)

NEW reformulation: (BIND) `|N_{ℚ(ζ_n)/ℚ}(Σ_{i∈S}ζ^i)| = |Res(x^{n/2}+1, f_S)|`, `f_S=Σ_{i∈S}x^i` a
**0/1 (Littlewood-type) polynomial**; `|N| ≈ M(f_S)^{n/2}·U(S)` with `M`=Mahler measure dominating.
The §5.0 hope (house bound loose by ~2⁶¹ ⟹ structure-aware bound proves `|N|<p`) is **REFUTED** by
the flat-polynomial literature: `M(f_S)` of 0/1 polys is `Θ(√|S|)` and **saturated** (flat
Littlewood polys exist; Choi–Erdélyi `M/√n>0.954`), so `|N(β_S)|` reaches the AM-GM bound
`|S|^{n/4}` up to a lower-order deficit. Verified (`probe_flat_littlewood_norm.py`): Rudin–Shapiro
0/1 subset gives `|N|>p` at n=128. So §5.0 cannot be closed by a norm UPPER bound — it reduces to
the COUNTING (#non-antipodal S with `p|N` at the binding band) = the BGK √-cancellation. All on disk.

| # | paper | id | bearing |
|---|---|---|---|
| ML1 | Beck (et al.), **Flat Littlewood Polynomials Exist** | arXiv **1907.09464** | flat ±1 polys with sup-norm `≤Δ√n` exist ⟹ Mahler measure `~√n` achievable ⟹ AM-GM/house bound for (BIND) is tight; the structure-aware-bound route cannot beat it. |
| ML2 | **Mahler measure of the Rudin–Shapiro polynomials** | arXiv **1406.2233** | explicit flat family; `M~√(2n/e)` (Saffari). The extremal 0/1 sets for the (BIND) norm. |
| ML3 | **Asymptotic value of the Mahler measure of Rudin–Shapiro** | arXiv **1708.01189** | proves `M(RS_n)~√(2n/e)` — quantifies the saturation (deficit from `√n` is the constant `√(2/e)`, lower-order). |
| ML4 | **Mahler's problem and Turyn polynomials** | arXiv **2405.08281** (2024) | newest on extremal/flat Mahler measure — the sharp constants the (BIND) max-norm needs. |
| ML5 | **Distribution of mixed character sums and extremal problems for Littlewood polynomials** | arXiv **2510.06161** (2025) | ties Littlewood-extremal problems to character sums — the bridge between the Mahler lens and the BGK character-sum lens (same wall, two communities). |

**Honest net:** the Mahler/Littlewood lens is a genuine NEW equivalent framing (different community, ML5 even bridges to character sums), and it DECIDES the §5.0 norm-bound sub-question NEGATIVELY: flat polynomials obstruct any `|N|<p` upper bound, so the wall is the counting/√-cancellation, not a loose house bound.

## 2026-06-15 — eprint 2025/2110 (Hab25, MCA-for-RS) OBTAINED + read in full
At ~/papers/arklib/eprint-2025-2110-Hab25.pdf. VERDICT: NOT a bypass. Proves RS satisfies MCA exactly UP TO the
Johnson radius γ=1−√(1−δ) (confirms ACFY24 conjecture), bound |E|≤(ℓ⁷/3)(ρn)², ℓ=(m+1/2)/√ρ — "essentially the
same as ordinary CA in BCI+20." Method: GS list-decoder over F_q(Z). Zero window-interior content; window past
Johnson for explicit RS remains the open core. Verbose update w/ BCH+25 (2025/2055) improvements promised.
Extraction: docs/kb/hab25-2025-2110-MCA-for-RS-extracted.md.

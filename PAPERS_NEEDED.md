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
## 2026-06-14 (#407) — the SHARP residual object: growing-n Gauss-period sup-norm (5 new papers)

This session re-derived (from independent probes, `scripts/probes/probe_moment_growth_law_407.py`) that
the prize floor is, *exactly*, the worst-case incomplete subgroup sum
`B(μ_n) = max_{b≠0}|Σ_{x∈μ_n} e_p(bx)|`, and that **`b ↦ Σ` is constant on μ_n-cosets** (proven:
`GaussPeriodCosetReduction.eta_mul_invariant`), so `B = max` over the **`m=(p−1)/n` Gauss periods** of
the order-`n` subgroup. The empirical law is `B = (1+o(1))·√(n·log₂((p−1)/n))` (constant ≈ 1, n=8..128).
The residual is therefore the **growing-n distribution / sup-norm of Gauss periods** = the generalized
Paley-graph eigenvalue (Paley Graph Conjecture). The 5 papers below bear *directly* on that object (none
already in `docs/references/proximity-gap-paley-spectrum/`; Kunisky 2303.16475 is already on disk, excluded).

| # | paper | id | URL | bearing on the residual |
|---|---|---|---|---|
| P1 | **Kowalski–Untrau, *Ultra-short sums of trace functions*** | arXiv **2302.13670** | https://arxiv.org/abs/2302.13670 | equidistribution of incomplete subgroup/trace sums as the length grows — the exact object `η_b`; gives the *fixed-n* hypocycloid limit. The growing-n sup-norm is the gap. |
| P2 | **Kowalski–Untrau, *Wasserstein metrics and quantitative equidistribution of exponential sums over finite fields*** (2025) | arXiv **2505.22059** | https://arxiv.org/abs/2505.22059 | **the frontier**: *quantitative* (Wasserstein) equidistribution rate for these sums — the only route to a growing-n tail/sup-norm bound. Get full PDF; check if the rate is uniform enough to bound `max_b` at `n=2^32`. |
| P3 | **Habegger, *The Norm of Gaussian Periods*** (Q. J. Math 2018) | arXiv **1611.07287** | https://arxiv.org/abs/1611.07287 | rate of convergence in **Myerson's conjecture** for Gauss-period norms — directly the resultant/transfer object `∏_j η_j = Res(f_c, X^n−1)` (`CharSumTransferNoGo`); the norm controls the char-0→F_p transfer threshold. |
| P4 | **Garcia et al., *Visual aspects of Gaussian periods and analogues*** (IJNT 2024) | arXiv **2308.05220** | https://arxiv.org/abs/2308.05220 | the limiting **geometry** (hypocycloid / bounded support) of the period distribution for fixed n; documents *why* fixed-n gives `B=O(√n)` and growing-n is the open inflation. |
| P5 | **Randomstrasse101, *Open Problems of 2025*** (Paley-graph problems 25–29) | arXiv **2603.29571** | https://arxiv.org/abs/2603.29571 | compiles the Paley-graph clique/eigenvalue open problems — confirms `B≤2√n ⟺ Ramanujan` and the SoS `O(p^{1/2−ε})` clique conjecture are *recognized 2025 open*, i.e. the prize floor is not a local gap but a frontier wall. |

**Honest scope:** P1/P4 give the *fixed-n* answer (`B=O(√n)`, bounded hypocycloid); P2 is the only
*quantitative growing-n* lead and is the one to read in full; P3 controls the *transfer* (Myerson norm);
P5 certifies the wall is a named open problem. None is a closure — consistent with this session's
moment-arrow NO-GO (`probe_moment_growth_law_407.py`: the only elementary handle provably overshoots).

### 2026-06-14 (#407) — two more, the live-literature confirmation of the wall
- **Shparlinski, *Open Problems on Exponential and Character Sums*** — https://web.maths.unsw.edu.au/~igorshparlinski/CharSumProjects.pdf — the canonical open-problem list; the growing/small-subgroup incomplete-sum sup-norm (the prize residual) is listed open. Confirms the prize floor is a named open problem, not a local gap.
- **Bourgain–Glibichuk(–Konyagin), *Bounds on exponential sums over small multiplicative subgroups*** — arXiv **0705.4573** — establishes nontrivial cancellation only for `|H| ≫ p^{3/7}` (later `p^{1/4}` via di Benedetto). Prize `n~p^{1/5}` is BELOW these thresholds ⟹ no published bound applies — the precise statement of the wall.

## 2026-06-13 (#407 tangent) — the IN-REGIME toolbox (5 new, the n<p^{1/4} side)

This session derived a **new exact identity** (`probe_autocorrelation_identity_407.py`, all checks 1e-14):
the Gauss-period power-spectrum autocorrelation factors as `A_h = m·conj(τ_h)·T_h` with `τ_h` the Gauss
sum (`|τ_h|=√p` EXACTLY, Weil/Deligne, proven) and `T_h = Σ_{w∈μ_n} χ^h(1−w) = (1/m)Σ_i J(χ^i,χ^h)`
the **subgroup tangent sum**. Since the Gauss factor is perfectly flat, the entire house concentration
is carried by `T_h` — relocating the open core onto the multiplicative tangent geometry of `{1−w:w∈μ_n}`
(an average of Jacobi sums). The papers below are the **in-regime** tools for that object (the prize has
`n≈2^30 < p^{1/4}≈2^39`, so the BGK/Burgess additive lineage is *out of regime* — re-confirmed). These 5
are NOT already on disk (verified distinct from the 2026-06-14 set and the BGK/Shparlinski entries above).

| # | paper | id | URL | bearing |
|---|---|---|---|---|
| T1 | **Ostafe–Shparlinski–Voloch, *Weil sums over small subgroups*** (2022) | arXiv **2211.07739** | https://arxiv.org/abs/2211.07739 | the ONLY recent paper targeting `\|G\|<p^{1/4}` (where Weil/√p is vacuous): bounds `Σ_{x∈G}χ(f(x))` via alg-geom + additive combinatorics. `T_h=Σ_{w∈μ_n}χ^h(1−w)` IS this object (f=1−w). Asymptotic (o(1)/p^ε), not effective at the instance — but the right surface. |
| T2 | **Rojas-León, *Equidistribution and independence of Gauss sums*** (2022, rev 2024) | arXiv **2207.12439** | https://arxiv.org/abs/2207.12439 | the only relations among the Gauss-sum family `{τ(χ^j)}` are conjugation / Galois / Hasse–Davenport ⟹ joint equidistribution. Characterizes the correlation structure of the `τ_j` whose DFT is `η_b` — exactly the "incoherence" the house needs. Qualitative (q→∞, no rate). |
| T3 | **Lu–Zheng, *On the distribution of multivariate Jacobi sums*** (2020/2021) | arXiv **2005.14358** | https://arxiv.org/abs/2005.14358 | normalized (multivariate) Jacobi sums equidistribute on the torus as q→∞. `J(χ^i,χ^h)` is the exact summand of `T_h`; the most on-point recent paper for the multiplicative/tangent side. No discrepancy rate. |
| T4 | **Fu–Lau–Li–Xi, *Equidistribution of Kloosterman sums over function fields*** (2024, IMRN 2025) | arXiv **2406.10106** | https://arxiv.org/abs/2406.10106 | best *effective* (explicit-error) Sato–Tate of the five + a *joint* law for two sums — the methods template for an effective Erdős–Turán/discrepancy attack on the `{χ̄(b)τ(χ^j)}` phases. Function-field, angle-distribution (not single max-modulus). |
| T5 | **Di Benedetto–Garaev–García–González-Sánchez–Shparlinski–Trujillo, *New estimates for exponential sums over multiplicative subgroups and intervals*** (2020) | arXiv **2003.06165** | https://arxiv.org/abs/2003.06165 | current SOTA additive subgroup-sum exponent `\|Σ\|≤H^{1−31/2880+o(1)}` — but needs `H>p^{1/4}`, so OUT of regime at the prize. Included to pin *exactly why* the standard machinery stops, i.e. the boundary the prize sits beyond. |

**Honest scope:** T1 is the right surface (small-subgroup multiplicative), T4 the effective-method template;
T2/T3 describe the exact algebraic objects but are qualitative; T5 delimits the wall. None effective at
`p≈2^158`. The residual — an effective bound on `B`/`T_h` in the `n<p^{1/4}` regime — is unchanged-open.
(Deliberately NOT slotted, to save re-search: flat/ultraflat-polynomial lineage el-Abdalaoui–Nadkarni
arXiv:2504.21499, 1402.5457 — about ±1 Littlewood coeffs, no link to the Gauss-sum unimodular sequence;
house *lower* bounds Pritsker 2101.06710, Munsch 1805.07163 — wrong direction; Garcia–Eischen 2012.10015
visual survey, no theorems.)

### 2026-06-13 (#407) — the LACUNARY reframing moves the core OFF the analytic wall
The session's deliverable (`scripts/probes/RESULTS-407-LACUNARY-RIGIDITY.md`,
`ArkLib/.../ProximityGap/DyadicLacunaryDeltaStar.lean`) recasts the prize floor as a
**lacunary-polynomial / cyclotomic-rigidity** count (NOT the incomplete-sum sup-norm).
Two refs underpin the moment-method anchor and the average-size confirmation (add if absent):
- **Garcia–Lorenz–Todd, *Moments of Gaussian Periods and Modified Fermat Curves*** — arXiv **2112.13886** (Ramanujan J. 2025) — the 4th absolute moment `V_4 = E(μ_d)` is an exact modified-Fermat-curve point count; the rigorous backbone of the moment method (fixed `d`).
- **Habegger, *The Norm of Gaussian Periods*** — arXiv **1611.07287** (Q. J. Math. 2018) — `m(1+X_1+…+X_{f−1}) ≤ ½ log f`: the *geometric mean* of `|η_b|` is `√f`-controlled (average-size confirmation; fixed odd prime `f`, no sup-norm).
These confirm `√(n log)` is correct *on average* but unreachable as a *max* — exactly why the
deliverable bypasses the analytic route via the `e_t`-homogeneity coset-rigidity engine instead.

### 2026-06-13 (#407) — coding-theory reformulation refs (the count = binary RS codewords)
The floor = #{weight-a 0/1 codewords of RS[n,n-t+1]} = #{subsets of μ_n with t-1 vanishing power
sums}. Decisive refs (verdict: count is OPEN for t,a=Θ(n) on explicit μ_n; = the wall):
- **Ben-Sasson–Kopparty–Radhakrishnan, *Subspace Polynomials and Limits to List Decoding of RS*** (IEEE-IT 56(1) 2010) — https://www.math.toronto.edu/swastik/rsld.pdf — for explicit ADDITIVE/subspace domains the near-codeword count is SUPER-POLYNOMIAL just past Johnson. Cautionary precedent; additive not multiplicative, so does NOT settle the μ_n (dyadic FFT) case — exactly the open question.
- **Kumar–Senthil Kumar, *Note on vanishing power sums of roots of unity*** — arXiv:1503.07281 — closest to the power-sum formulation; SINGLE power, existence/characterization only, NO count (the t=Θ(n) simultaneous count is the open extension).
- **Li–Wan exact subset-sum fibre** `C(s,k)/s` (JCTA 119(1) Cor 1.4) — the t=2 (single-constraint) slice, proven in-tree (`subsetSum_fibre_card_mul`).

### 2026-06-13 (#407) — ideal-lattice / lattice-crypto domain (the GoN reformulation's literature)
The residual reformulated as a cyclotomic prime-ideal house-count (lattice-crypto territory). Sweep
verdict: the fully-split case q≡1 mod 2^μ (N(𝔮)=q) = the PRIZE = the explicitly-OPEN hard case.
- **Fukshansky–Petersen, *On Well-Rounded Ideal Lattices*** — arXiv:1101.4442 (IJNT 2012) — cyclotomic ideal lattices are WELL-ROUNDED (λ_1=…=λ_{n/2}); |minimal vectors|=r_1+r_2. PROVEN shape fact for 𝔮; does NOT bound the box point-count.
- **Cheng et al., *Solution counts and sums of roots of unity*** — J. Number Theory (2022), https://doi.org/10.1016/j.jnt.2022.01.... — EQUATES the additive p-defect count to lower bounds on the house of sums of roots of unity (the exact dictionary); no worst-case poly bound.
- **Pan–Xu–Wadleigh–Cheng, *Ideal SVP over random rational primes*** — arXiv:2004.10278 (EUROCRYPT 2021) — cyclotomic prime-ideal SVP poly only for non-split q (q≡±3 mod 8); EXPLICITLY excludes N(𝔮)=q (fully split) = the prize regime. "will not improve matters if q splits completely."
- **Cui–Li–Zhuang, *Principal ideal & ideal-SVP over rational primes in power-of-2 cyclotomics*** — arXiv:2601.07511 (2026) — exact λ_1 for non-split classes only; fully-split worst-case left open.
- **Felderhoff–Pellet-Mary–Stehlé–Wesolowski, *Ideal-SVP Hard for Small-Norm Uniform Prime Ideals*** — ePrint 2023/1370 (TCC 2023) — worst-case-to-average over uniform small-norm prime ideals; assumes their distribution.
Verdict: NO known worst-case (or almost-all-q) bound on #{α∈𝔮: house≤B~log q} by poly/q^{o(1)} for split q. The prize regime is the recognized open case in the ideal-lattice domain too.

## 2026-06-13 (#407 FIXED-INDEX literature sweep) — REGIME PIN + fresh 2024–2026 leads (the "positive-proportion re-opens Burgess" directive, RESOLVED)

**Directive tested (and REFUTED arithmetically — do not re-chase):** a #407 framing proposed that holding
the security index `m=(p−1)/n≈2^128` *constant* as the FFT domain `n=2^μ` grows makes `μ_n` a
**positive-proportion** subgroup (`n=Θ(p)`, `n≫√p`), which would put **Burgess / large-sieve / large-subgroup
sum-product** bounds (e.g. `B≤p^{1/4}√n`, nontrivial iff `n>√p`) *in regime* and possibly close the floor.
This is an **arithmetic error**, independently re-verified this session (`scripts/probes/_wf407_regime_check.py`):
`p−1=n·m` with **both** `n=2^μ` (`μ≤40`) and `m≈2^128`; "m constant" ≠ "n=Θ(p)" (that needs `m=O(1)`, but
`m=2^128` is a *huge* constant and `n≤2^40 ≪ m`). So **`n` is the SMALL factor**: density `n/p=1/m=2^{−128}`
(the **thinnest** regime in the campaign, independent of μ), exponent `n=p^{μ/(μ+128)} ∈ [p^{0.072}, p^{0.238}]`
— all **below `p^{1/4}`**, and `n≥√p` is false by `≥2^{44}`. The large-subgroup regime (`n>√p`) is **empty of
prize instances**. Cf. `docs/kb/deltastar-407-positive-proportion-premise-refuted-2026-06-13.md` and the #407
owner comment confirming Lane A (constant-index energy) survives only as a *recognized-hard* lane, its
Plünnecke–Ruzsa sub-route **vacuous** (`|μ_n+μ_n|≈p`, doubling `K≈m`). **The corrected regime is THIN**, so the
sweep below is scoped to thin-subgroup (`n<p^{1/4}`) tools, NOT Burgess/large-sieve.

**Net of the fresh 2024–2026 sweep: NO breakthrough.** No 2024–2026 paper gives `√`-cancellation, the
`√(n·log m)` sup-norm, or even a power-saving for *single-frequency* subgroup sums below `p^{1/4}`. The
freshest "small-subgroup" SOTA (`2401.04756`) is **expository** (re-proves BGK, no new exponent). The 7 NEW
catalog entries below are the closest live surfaces; each is honestly off-target in a specific way.

| # | paper | id | URL | exact bearing / why it does NOT close |
|---|---|---|---|---|
| F1 | **Shparlinski et al., *Equations and character sums with matrix powers, Kloosterman sums over small subgroups, and quantum ergodicity*** (IMRN 2023) | arXiv **2110.10941** | https://arxiv.org/abs/2110.10941 | **The closest "below-√p" thin analytic surface.** Abstract: "a bound on Kloosterman sums over small subgroups, of size **below the square-root threshold**." This is the thin regime the prize lives in — but the object is the **two-frequency Kloosterman** sum `Σ_{x∈G}e_p(ax+b/x)`, not the **single-frequency** Gauss period `η_b=Σ_{x∈μ_n}e_p(bx)` the floor needs. Adjacent geometry, method = alg-geom × additive-combinatorics; its exponent does not transfer to `η_b`. Get full PDF, check the exact `|G|=p^α` range. |
| F2 | **Shkredov–Shparlinski et al., *Polynomial Values in Small Subgroups of Finite Fields*** | arXiv **1401.0964** | https://arxiv.org/abs/1401.0964 | Foundational small-subgroup paper (the lineage 2110.10941/2003.06165 descend from); fixes the `|G|<p^{1/4}` toolbox (Stepanov + Cauchy–Schwarz amplification). Confirms `η_b` over thin `μ_n` has **no published nontrivial bound** — pins the wall's birth, not a closure. |
| F3 | **Macourt–Shkredov–Shparlinski (?), *Multiplicative Energy of Shifted Subgroups and Bounds on Exponential Sums with Trinomials*** (Canad. J. Math 2025) | arXiv **1701.06192** | https://arxiv.org/abs/1701.06192 | **Freshest energy-route SOTA** for the Lane-A object: a *new bound on collinear triples in subgroups* (= the additive-incidence structure that controls `E^+(μ_n)` and the trinomial sum). BUT (i) it is **multi-frequency (trinomial)**, and (ii) the collinear-triple/energy gain is in the `|H|` range where energy is *anomalous*; at prize-thin `n` the in-tree value is the trivial char-0 `E^+=3n²−3n` (verified `=720` at n=16) — the energy route delivers only the Parseval RMS `√n`, never the `√(n log m)` MAX. Confirms the energy wall, sharpens nothing at the floor. |
| F4 | **Kim–Yip–Yoo, *Multiplicative irreducibility of shifted multiplicative subgroups*** (2026) | arXiv **2602.20919** | https://arxiv.org/abs/2602.20919 | Freshest (2026) structural result on `μ_n` shifts (the `{1−w:w∈μ_n}` tangent geometry of the autocorrelation identity). Proves shifted subgroups can't factor as Cartesian products — but requires `n` **not too small** (polynomial-in-p thresholds), i.e. **out of the prize-thin regime**; no energy/sum bound. A structural-irreducibility input for the Action-Orbit lane (B), not the floor. |
| F5 | **Demirci Akarsu, *Finite-dimensional distributions for short incomplete Gauss sums*** (2025) | (search: Demirci Akarsu 2025) | — | Freshest on the **value-distribution** thread (successor to 1207.1607). Gives a *limit law* (bounded, finite support, Gumbel-type tail) for **interval** incomplete Gauss sums `Σ_{x<N}e_p(x²α)` — a **different object** (sum over an *interval*, not a *multiplicative subgroup*). Reconfirms the fixed-shape distributional picture (cf. O4/SZ4); the **growing-`n` sup-norm** is the gap it does not bridge. |
| F6 | **Lamzouri et al., *Large quadratic character sums* + *Note on large quadratic character sums*** (2025) | arXiv **2509.07651**, **2510.09005** | https://arxiv.org/abs/2509.07651 | **Refutation-oracle (the floor SURVIVES it).** Newest Ω-results pin the max partial sum between **Paley `Ω(√q·log log q)`** and **Pólya–Vinogradov `O(√q·log q)`** — i.e. a *full* `log` outside the `√`. If the *subgroup* Gauss period obeyed the PV law it would be `√n·log m`, **falsifying** the `√(n·log m)` floor. Probe `_wf407_floor_logpower.py` shows it does **not**: `B/√(n·ln m)∈[1.08,1.47]` (flat, n=16..1024) while `B/(√n·ln m)` *drifts down* (0.52→0.49) — the subgroup sum's log is **inside** the sqrt (half-power milder than PV). So the large-sums Ω-machinery does not refute the floor; it certifies the floor's log-power is correct. |
| F7 | **Shkredov, *On the distribution of additive energy revisited*** (2026) | arXiv **2602.01781** *(=SZ5, already catalogued)* | https://arxiv.org/abs/2602.01781 | Re-surfaced as the energy-distribution SOTA; record `E(Γ)≪|Γ|^{5/2}` needs `|Γ|≤p^{2/3}` and the `√p`-threshold refinement needs `|Γ|=O(√p)` — **both far above** prize-thin `n≤p^{0.238}`. No prize-regime gain. (Listed for completeness; not a new row.) |

**Honest scope (decisive):** the regime correction does **not** re-open Burgess/large-sieve — the prize subgroup
is the *thinnest* (`density 2^{−128}`, `n<p^{1/4}`), so those tools stay out of regime (large-sieve route
separately walled, `deltastar-407-largesieve-amplification-nogo`). Across the freshest 2024–2026 literature the
single-frequency thin-subgroup sup-norm `B=max_b|η_b|` has **no nontrivial published bound** (SOTA `2003.06165`
needs `n>p^{1/4}`; `2110.10941` is the only "below-√p" result and it is *Kloosterman*, two-frequency). The one
**positive** finding is a *refutation that didn't fire*: the 2025 large-quadratic-sums Ω-results (F6) would
falsify the `√(n·log m)` floor if the subgroup sum obeyed the Pólya–Vinogradov `√q·log q` law — measured, it
does **not** (log is inside the sqrt), so the floor's exact log-power is *confirmed* against the strongest
known large-values oracle. No closure; the thin-regime `√`-cancellation core is unchanged-open.

## 2026-06-14 (#407 `anchors-import` J/H4) — DROPPED §8 external anchors, precise statements + verdicts

Per-anchor literature acquisition for the anchors dropped from #407 §8's table. Verdict per anchor in
`docs/kb/wf407-anchors-import-dropped-external-anchors.md`; elementary kernel in
`Frontier/WF407_AnchorsImport.lean`; regime probe `scripts/probes/wf407_anchors-import_regime.py`. Net:
**WALLED** — none supplies the prize `B`-form (linear Gauss period). All open-access; fetch if absent.

| # | paper | id | exact statement | verdict |
|---|-------|----|-----------------|---------|
| AN1 | **Ostafe–Shparlinski–Voloch, *Weil Sums over Small Subgroups*** | arXiv **2211.07739** (MPCPS 176 (2024) 39–53) | bounds `Σ_{x∈G}ψ(f(x))` nontrivially where classical Weil is trivial (small `\|G\|`); requires `deg f = d ≥ 2`, `f ≠ g(x^k)`; **asymptotic** (`o(\|G\|)`), not effective. | **Wrong shape**: prize `B` is the linear `f(x)=b·x` (`d=1`), excluded by `d ≥ 2`. Matches only the tangent sum `T_h`, asymptotically. (= `WF407_AnchorsImport.osv_degree_excludes_linear_prize_object`.) |
| AN2 | **Konyagin–Shparlinski–Vyugin, *Polynomial Equations in Subgroups and Applications*** | arXiv **2005.05315** (LNM "Number Theory…"; Springer 2022) | **Thm 1.2:** `Σᵢ#{(u,v)∈𝒢²:Pᵢ(u,v)=0} < 12mn(m+n)g·h^{5/3}·t^{2/3}`, valid `12p^{3/4}h^{−1/4} ≥ t ≥ max{h²,c₀}`. **Conj 1.3 (open):** `∃ε₀,A`: for `#𝒢 ≤ p^{ε₀}`, `(α₁₁u−α₁₂)/(α₂₁u−α₂₂)=v` has `≤A` sols `u,v∈𝒢`. **Thm 1.6 (cond. on 1.3):** Markoff `#(ℳₚ∖𝒞ₚ) ≤ (log p)^B`, `B=16 log A+c`. | **Right regime, wrong axis**: `t ≤ 12p^{3/4}` satisfied at prize (`a ≤ 40`), but `t^{2/3}` is an algebraic-coincidence **count** (cluster 3, wall W1), not the `B`-form. Conj 1.3 (subgroup Möbius coincidence, "production regime" `#𝒢 ≤ p^{ε₀}`) is **OPEN**. (= `WF407_AnchorsImport.ksv_upper_range_satisfied`, `ksv_count_exponent_lt_one`.) |
| AN3 | **Corvaja–Zannier, *Greatest common divisors of u−1,v−1…*** | JEMS **15 (2013)** 1927–1942 | gcd `(u−1,v−1)` / subgroup poly-eqn `t^{2/3}`-type count (the ancestor of KSV Thm 1.2). | **Subsumed by KSV** (same count face, strictly weaker). |
| AN4 | **Makarychev–Vyugin, *Solutions of Polynomial Equations in Subgroups of 𝔽_p*** | Arnold MJ **5 (2019)** 105–121 | `t^{2/3}` poly-equation solution count in `F_p` subgroups (the other ancestor of KSV). | **Subsumed by KSV** (count face). |
| AN5 | **Myerson, *How small can a sum of roots of unity be?*** (+ Lehmer lacunary resultant maxima) | (classical; see also 2104.15057 small-five) | small-sum `f(k,n) ∈ [k^{−n}, n^{−k/4+o(1)}]` (upper only `k,n` even); companion house `\|N(Σ_{i∈S}ζ_n^i)\| ≤ (#S)^{φ(n)} ≤ n^{n/2}`. | **Same wall** as `HeightGateNormBound`: the house IS `(#S)^{φ(n)}`; Myerson refines the **min** (wrong direction), house `n^{n/2} > p` for all `a ≥ 8`. Height-obstruction wall. (= `WF407_AnchorsImport.myerson_house_exponent_eq_half`.) |
| AN6 | **Chang–Shparlinski / Kerr–Macourt bilinear** (lineage BGK 0705.4573) | — | sub-`√q` double sums need two density-`> p^{3/7}` variables. | **Out of regime** (already `WF407_T02Shkredov.bilinear_factor_below_quarter`): `μ_n` has no second density-`p^{3/7}` factor at `a ≤ 40`. W4 / density gate. |

**Honest scope:** WALLED. OSV = wrong shape, KSV/CZ/MV = right-regime-but-count-not-`B` (Conj 1.3 open),
Myerson = height-obstruction wall, bilinear = density gate. New avenue: KSV Conj 1.3 is an *in-regime,
unconditional-if-resolved* bilinear coincidence count lever (feeds the super-code list bridge 407-T11);
OSV is the correct surface for `T_h` (effectivity unchecked). The prize `B`-form is unchanged-open.

## 2026-06-14 (A34) — lacunary cyclotomic resultant maxima for the [KKH26] collision object

A34 (merged `357-T13 / 334-T15`) chased the lacunary cyclotomic resultant / Mahler-measure literature
(Myerson, Lehmer-adjacent) for a sharp upper bound on `|Res(Φ_{2^m}, g)|` for sparse `±1` polynomials
`g`, to open the `s = 128` [KKH26] ceiling rows below the prize cap `q < 2^256` **without** Thorner–Zaman.

**Verdict (PARTIAL — no new paper needed for the gain).** The operative literature object is
**Landau's inequality** `M(g) ≤ ‖g‖₂` (Mahler measure ≤ ℓ²-norm), already in Mathlib
(`Polynomial.mahlerMeasure_le_sqrt_sum_sq_norm_coeff`) and already in-tree
(`SharpResultantBound.lean`, `KKH26.cyclotomicLandauSqBound_proved`). For the [KKH26] *collision*
resultant `N = Res_ℤ(R, Φ_{2^m})`, `R` a `±1,0` poly with `‖R‖₂² ≤ 4r`, the Landau/Parseval+AM-GM
envelope is `|N|² ≤ (4r)^{2^{m-1}}` and it is **sharp on this class** (probe
`scripts/probes/sweep_A34_lacunary_maxima.py`: worst-case geo/arith ratio of `|R(ζ^{odd})|² ≈ 1`,
AM-GM tight ⟹ no constant-factor improvement below `(4r)^{h/2}`). The `r`-refinement (vs the in-tree
`r = h` freeze) opens `s = 128` at `ρ ≤ 1/4` (`Frontier/Sweep_A34_LacunaryResultantS128.lean`,
axiom-clean), but **not** `ρ = 1/2` at `s = 128` nor any `s = 256` row.

- **Myerson, *How small can a sum of roots of unity be?*** (Amer. Math. Monthly 93 (1986) 457–459) —
  re-confirmed (cf. AN5): refines the **minimum** sum of roots of unity, the *wrong direction* for an
  upper bound on `|Res|`. Not needed.
- **Lehmer-adjacent / lacunary Mahler maxima** (e.g. Boyd, *Speculations concerning the range of
  Mahler's measure*; Smyth surveys) — no upper bound on `M(g)` for sparse `±1` `g` tighter than the
  trivial `‖g‖₂`; Landau is sharp here. Not needed for the proven bracket; the **prize-proper**
  asymptotic `s = 2^μ → ∞` rows (polynomial field size `p = Θ(n^β)`) still require Thorner–Zaman
  PNT-in-APs (`KKH26PolyFieldCeiling.lean`), unchanged.

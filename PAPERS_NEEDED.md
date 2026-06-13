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

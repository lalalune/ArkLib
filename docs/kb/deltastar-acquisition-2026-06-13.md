# δ* Research Acquisition Manifest (2026-06-13)

Exhaustive literature-acquisition pass for the proximity-gap prize program (#389 / #371),
executed against the identifier list in
[`deltastar-literature-findings-2026-06-13.md`](deltastar-literature-findings-2026-06-13.md)
and [`deltastar-research-map.md`](deltastar-research-map.md). **44 new open-access PDFs
acquired** into `~/papers/arklib/` (74 total on disk). This page is the index + the
remaining-gaps list + the verbatim prize statements recovered this pass.

## 0. The grand challenges — verbatim from proximityprize.org (recovered this pass)

The prize site states the two challenges with **exactly these parameters** (note this is the
authoritative framing; subtly sharper than some in-tree paraphrases):

> **Challenge 1 — Grand MCA Challenge.** Determine the largest `δ*_C ∈ [0,1]` such that the
> mutual-correlated-agreement error `ε_mca(C, δ*_C) ≤ ε*` for Reed–Solomon codes with rate
> `ρ(C) ∈ {1/2, 1/4, 1/8, 1/16}` and `ε* = 2^{-128}`.
>
> **Challenge 2 — Grand List Decoding Challenge.** Determine the largest `δ*_C ∈ [0,1]` such
> that the list-decoded set satisfies `|Λ(C^{≡m}, δ*_C)| ≤ ε* · |F|` for the **same** code
> family and `ε* = 2^{-128}`.

Prize parameters: pool `$1,000,000`; target rates `{1/2, 1/4, 1/8, 1/16}` (**constant** rate —
the hard regime, not constant-dimension); `ε* = 2^{-128}`; field `|F|` "sufficiently large".

**Key structural reading for a unifying conjecture (the /goal target).** Both challenges ask
for the *same* `δ*_C` shape on the *same* family, and Challenge 2 is stated on the **interleaved**
code `C^{≡m}` with list bound `ε*·|F|` (a *field-size* bound, not poly(n)). The §5 LD⇒MCA
collapse of ABF26 is the bridge: a conjecture pinning `|Λ(C^{≡m}, δ)|` as an explicit function of
`δ` that crosses `ε*·|F|` at the *same* `δ*` where `ε_mca` crosses `ε*` solves both at once. Any
candidate must therefore be a *single closed `δ*(ρ)` law* valid at the four constant rates.

## 1. Newly acquired this pass (44 PDFs, all `%PDF`-verified in `~/papers/arklib/`)

### Smooth-domain additive energy (#389 core quantity `E⁺(μ_n)`)
| file | id | what |
|---|---|---|
| `arxiv-1102.1172-Shkredov.pdf` | 1102.1172 | `E⁺(G) ≪ \|G\|^{22/9}` for subgroups, `\|G\|≪p^{1/2}` |
| `arxiv-1712.00410-MRSS.pdf` | 1712.00410 | Murphy–Rudnev–Shkredov–Shteinikov SOTA energy `49/20` |
| `arxiv-1507.05548-MRSS2.pdf` | 1507.05548 | MRSS companion (few-products / energy) |
| `arxiv-1701.06192-MacourtShkredovShp.pdf` | 1701.06192 | Macourt–Shkredov–Shparlinski energy of subgroups |
| `arxiv-1604.08469-AksoyYazici.pdf` | 1604.08469 | sum–product / energy machinery |
| `arxiv-1808.05543-Rudnev.pdf`, `arxiv-2303.00330-Rudnev2.pdf` | 1808.05543, 2303.00330 | Rudnev point–plane incidence (the energy engine) |
| `arxiv-2304.13801-Yip.pdf` | 2304.13801 | subgroup is **not** a sumset (`G≠A+A`) — superpoly evidence for ℓ-fold sumset |
| `arxiv-1504.04522-Shkredov2.pdf` | 1504.04522 | Shkredov energy/structure |

### Character sums over small subgroups (face (ii); confirms the no-go)
| file | id | what |
|---|---|---|
| `arxiv-0705.4573-Kurlberg.pdf` | 0705.4573 | BGK exponent triple-exp small |
| `arxiv-2003.06165-KST.pdf` | 2003.06165 | Konyagin–Shparlinski–Trujillo explicit BGK `≈1.08e-2` |
| `arxiv-1712.00761-Mohammadi.pdf` | 1712.00761 | prime-power: bound needs `\|H\|≳q^{1/2}`, subfield-avoidance mandatory |
| `arxiv-2211.07739-OSV.pdf` | 2211.07739 | incomplete character sums |
| `arxiv-2401.04756-Kowalski.pdf` | 2401.04756 | Kowalski sums-of-products |

### Beyond-Johnson list decoding / line-in-ball (faces (i),(iv))
| file | id | what |
|---|---|---|
| `arxiv-2410.09031-FRSlistsize.pdf`, `arxiv-2502.14358-FRSlistsize2.pdf` | 2410.09031, 2502.14358 | folded-RS list-size lower bounds |
| `arxiv-2511.05176-DetRSLD.pdf` | 2511.05176 | deterministic RS list decoding (ECCC TR25-170) |
| `arxiv-2012.10584-LargeRadius.pdf` | 2012.10584 | large-radius list decoding |
| `arxiv-2206.05256-GenericRSMDS.pdf` | 2206.05256 | generic RS / higher-order MDS |
| `arxiv-2508.12548-LineInBall.pdf` | 2508.12548 | lines in Hamming balls |
| `arxiv-2601.10047-FoldedRS-SubspaceDesign.pdf` | 2601.10047 | **GG25/JLR26** optimal proximity gap, folded-RS via subspace designs (STOC'26) |

### Deep holes / roots of unity / vanishing sums (faces (iii),(iv); census)
| file | id | what |
|---|---|---|
| `arxiv-math9511209-LamLeung.pdf` | math/9511209 | **vanishing sums of roots of unity** — 2-power ⇒ antipodal-pair structure (census compression) |
| `arxiv-math9605216-LamLeungCharP.pdf` | math/9605216 | char-`p` analogue (extra `p`-axis) |
| `arxiv-2008.11268-ChristieDykemaKlep.pdf` | 2008.11268 | vanishing-sum robustness to weight 21 |
| `arxiv-1503.07281-PowerSumSystems.pdf` | 1503.07281 | power-sum systems |
| `arxiv-math0204052-Khovanskii.pdf` | math/0204052 | Khovanskii / sumset growth |
| `arxiv-1508.02804-ZhuWan.pdf` | 1508.02804 | **Zhu–Wan** error distance by `deg u`; char-2 parity (`q−k` vs `q−k−1`) |
| `arxiv-1612.05447-Kaipa.pdf` | 1612.05447 | deep holes of RS |
| `arxiv-2403.11436-FangXuZhu.pdf`, `arxiv-2509.08526-GuWangZhang.pdf` | 2403.11436, 2509.08526 | far-direction deep-hole exhaustiveness (`x^{q-2}` inverse map) |
| `arxiv-1806.00152-DistDist1.pdf`, `arxiv-2205.02277-DistDist2.pdf` | 1806.00152, 2205.02277 | RS distance distribution |
| `arxiv-1101.0289-SubsetSumSubgroups.pdf` | 1101.0289 | subset-sums over subgroups (the #389 deployed-halo object) |

### Littlewood–Offord / value-concentration on subgroup orbits (the new lever, face (iv))
| file | id | what |
|---|---|---|
| `arxiv-1803.02165-CillerueloGaraev.pdf` | 1803.02165 | **Cilleruelo–Garaev** concentration of points: rational map repeats on a subgroup orbit |
| `arxiv-1309.7378-GomezPerezShp.pdf` | 1309.7378 | Gómez-Pérez–Shparlinski value distribution |
| `arxiv-1907.02302-Merai.pdf` | 1907.02302 | Mérai concentration |
| `arxiv-1904.10425-FJLS.pdf`, `arxiv-1907.02575-LuhMeehanNguyen.pdf` | 1904.10425, 1907.02575 | inverse Littlewood–Offord counting |
| `arxiv-2106.04894-OminimalLO1.pdf`, `arxiv-2505.24699-OminimalLO2.pdf` | 2106.04894, 2505.24699 | o-minimal Littlewood–Offord |
| `arxiv-2505.23335-PolyLO1.pdf`, `arxiv-1909.02089-PolyLO2.pdf` | 2505.23335, 1909.02089 | polynomial Littlewood–Offord |
| `arxiv-1408.5681-RandomCosetWeights.pdf` | 1408.5681 | random-coset weight distribution |

## 2. Already on disk before this pass (kept)
ABF-relevant core already present: `eccc-tr25-169.pdf` (=BCHKS25 = ePrint 2025/2055, the barrier
+ **Conj 1.12** subgroup-sumset gating the upper bracket), `late2025/goyal_guruswami_eccc166.pdf`
(=GG25 = ePrint 2025/2054, near-capacity for folded/random only), `eprint-2025-2046.pdf`
(Crites–Stewart capacity-failure), `eprint-2026-858.pdf` / `eprint-2026-861.pdf` (Chai–Fan),
`eprint-2026-891.pdf` (Jo26), `arxiv-2304.09445-agl24.pdf` (AGL24 = merged Guo–Zhang journal),
`arxiv-2604.09724.pdf` (prime-field capacity counterexample), plus the protocol stack (BCIKS20,
STIR, WHIR, Basefold, Binius, LogUp, Spartan, Plonk, BCS16, Thaler).

## 3. Remaining gaps — IACR-only, blocked by Cloudflare (manual browser fetch needed)

The environment's network (curl + server-side WebFetch) is **fully Cloudflare-403'd against
`eprint.iacr.org`** this pass; authors link only to IACR. Fetch these manually in a browser and
drop into `~/papers/arklib/`:

| paper | id | priority | content available via |
|---|---|---|---|
| **ABF26** — Open Problems in LD & CA (the prize paper) | ePrint 2026/680 | ★★★ | statements recovered from proximityprize.org (§0 above) |
| **Hab25** — note on mutual correlated agreement | ePrint 2025/2110 | ★★ | Johnson lane; one residual now supplied by BCHKS25 |
| **Syndrome-Space Lens** (Okamoto) — *claims* complete resolution up to capacity | ePrint 2025/1712 | ★★★ review-flag | **adversarial read required** — incompatible with proven capacity-failure (Crites–Stewart/BCHKS25/Diamond–Gruen); locate the flaw at the rank-margin `Δ=t−d` boundary |
| **Diamond–Gruen** — `n^τ` proximity-gap refuted ∀τ (char-2) | ePrint 2025/2010 | ★★ | no ECCC mirror found |
| Bordage et al. | ePrint 2025/2051 | ★ | abstract html only on disk |
| Mohnblatt–Wagner — MCA ⇒ FRIDA | ePrint 2026/1055 | ★ | — |
| GMW — Lean4 round-by-round FRI soundness | ePrint 2025/1993 | ★ | formal substrate; check for a GitHub repo too |
| Fenzi–Sanso — small-field SNARGs less sound | ePrint 2025/2197 | ★ | — |

Paywalled (Elsevier; try arXiv preprint names if a residual needs them):
- **Li–Wan**, "k-subset sum over char-2 finite fields" (Finite Fields Appl. S1071579719300462) —
  char-2-native `C(n,k)/q` + Weil error; **strongest char-2 ℓ-word supply lever**.
- "a small multiplicative subgroup is not a sumset" (S1071579720300149) — superpoly evidence.

## 4. The exhaustive keyword search list used (for re-sweeps)
beyond-Johnson list decoding explicit Reed-Solomon · mutual correlated agreement proximity gap ·
additive energy multiplicative subgroup F_p · `E⁺(G)` Heath-Brown Konyagin Shkredov ·
incomplete character sums small subgroups BGK Bourgain-Glibichuk-Konyagin · vanishing sums of
roots of unity 2-power Lam-Leung · subset-sum over multiplicative subgroup · deep holes
Reed-Solomon far direction · error distance fixed degree Zhu-Wan char-2 · Littlewood-Offord
polynomial concentration subgroup orbit Cilleruelo-Garaev · folded RS subspace design capacity ·
proximity gap capacity barrier char-2 · subgroup-sumset conjecture BCHKS · line in Hamming ball
incidence · ℓ-fold sumset poly vs superpoly · FRS list size lower bound · syndrome space proximity
resolution.

---
*Net this pass: 44 open-access PDFs acquired; grand-challenge statements pinned verbatim; 8
IACR-only + 2 paywalled items flagged for manual fetch (the Syndrome-Space-Lens "complete
resolution" claim is the one to read adversarially first — if correct it closes the prize, so the
flaw must be located).*

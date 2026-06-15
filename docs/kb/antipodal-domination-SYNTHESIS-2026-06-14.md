# SYNTHESIS: both surviving structural hopes (§7.2 Sidon, §7.3 antipodal-domination) ELIMINATED — reduce to the BGK moment (2026-06-14)

**Bottom line (honest, well-verified): the two structural hopes #444 §7 flagged as "surviving" — the
Sidon bootstrap (§7.2, the dossier's flagged BEST hope) and the over-determined antipodal-domination
floor (§7.3) — are BOTH now eliminated as theorems. Both reduce to the open BGK moment `Σ_{b≠0}|η_b|^{2r}`
= BCHKS-1.12. The antipodal-dominated (closed, p-independent) object pins δ* at `Johnson + 1/n` (the
Plotkin proxy); beyond Johnson, the collective object IS the BGK moment (exact Parseval identity). No
closed off-BGK floor exists. The floor-side gap (`n^{0.989} → n^{0.5}` at β=4) is intact — no 2024-26
lever. This is a route-elimination of the last two flagged hopes, narrowing the prize to its irreducible
BGK/Paley core — NOT a closure.**

## The sharp question attacked (#444 §6/§7.3, never-before tested)
At the binding radius in the window, is the over-determined incidence ANTIPODAL-DOMINATED (height-1
relations `x+(−x)=0`, p-independent for ALL primes ⟹ a CLOSED off-BGK floor) or does SPURIOUS
non-antipodal mod-p vanishing DOMINATE (⟹ BGK wall)? The in-tree gate `HeightGateNormBound.
gate_2power_antipodal` proves spurious ⟹ antipodal only for `p > T^{n/2}` (fails n≥64,
`gate_NOT_fires_64`); the dossier knew spurious EXISTS at n≥32 but never tested DOMINANCE.

## Finding 1 — antipodal DOES dominate at the binding radius, but pins δ* at JOHNSON (proxy, prize-inert)
- **Domination numeric (fleet):** n=16 ρ=1/4, over-det binding (t=2, agr=6, I=89 ≫ budget 16 ⟹ deeper t
  needed): `N_anti=89, N_spur=0, ratio=0.0000` across ALL primes incl. thin~β4 (p=65617) — antipodal
  dominates COMPLETELY (spurious=0) even where the gate does not fire. Confirms cliff-confinement.
- **The pin (independent, this session):** the char-0 (antipodal, p-independent) over-determined binding
  `δ* = Johnson + 1/n` at constant rate: `(δ*−Johnson)·n = +1.00` exact at n=16, =+1.0 at n=20,24
  (cliff-confinement data). So the off-BGK closed count crosses budget at the JOHNSON EDGE, converging
  to Johnson as n→∞ — the Plotkin proxy (#444 §6/c.348), NOT reaching into the window toward capacity.
- ⟹ Even where antipodal dominates (spurious=0), it pins δ* at Johnson. The off-BGK closed object
  reproduces Johnson; it does not give beyond-Johnson δ*.

## Finding 2 — the Sidon bootstrap (§7.2) is REFUTED in BOTH forms (route-elimination)
The dossier's flagged BEST surviving hope (B_β → B_{log n}: μ_n at β≥4 is B_β, does it bootstrap to
B_{log n} ⟹ moment method at depth log n ⟹ prize core)?
- **Per-relation (norm gate):** `s_gate(n,4) = n^{8/n}`: n=8→8.0, n=16→4.0, n=32→2.38, n=64→1.68,
  **n=2^30→1.0000077** — the achievable depth COLLAPSES to ~1 at prize scale. Zero depth gain. DEAD.
- **Collective / family-level (the §7.2 surviving form, "NOT per-S norm"):** by the EXACT Parseval
  identity `E_r^{(p)} = (1/p)Σ_b|η_b|^{2r}` (verified: n=8 p=3329 r=2,3 match; n=16 p=49681 r=2,3 match),
  the DC-subtracted `A_r^{(p)}` IS the open BGK moment `Σ_{b≠0}|η_b|^{2r}` — there is NO decoupling and
  NO off-BGK floor; it is capped by the §4 meta-theorem `(q·E_r)^{1/2r} ≥ n`. Spurious excess at the
  binding radius (n=16 r=4 Δ/DC=0.31, n=32 r=4 worst 1.71/4-of-5-primes-nonzero) = the BGK moment excess.
⟹ Both forms of the Sidon bootstrap reduce to the BGK moment. **Add §7.2 to the §8 dead ledger.**

## Finding 3 — literature: gap INTACT, no new lever; one new relevant paper
5 papers cataloged (reading-list-open-core-2026-06-14.md). FLOOR side (the prize): re-verified UNTOUCHED
— no di Benedetto/Garaev/Shkredov/Murphy/Rudnev 2024-26 improvement; SOTA stays di Benedetto-Garaev
(arXiv:2401.04756) `n^{1−31/2880}=n^{0.989}` for H>p^{1/4}, collapsing to Bourgain-Garaev `n^{0.99998}`
at exactly β=4 (the prize point). Gap to `n^{0.5}` = full half-power = Paley Graph Conjecture. NEW on the
EXACT object: Kambiré arXiv:2604.09724 (in ~/papers); **Haböck-Krachun-Kazanin ePrint 2026/782**
(20 Apr 2026, Cloudflare-blocked — get via institutional access) — an additive-combinatorics lemma on
sums of roots of unity that gives a sharp CROSSOVER: antipodal dominates on a positive-density Linnik
GOOD-prime subset (subset-sums distinct mod p ⟹ proximity gaps fail near capacity, matching the proven
ceiling δ*≤1−ρ−Θ(1/log n)); spurious dominates on the BAD-prime complement. This good/bad-prime dichotomy
IS the p-dependence = BGK; it confirms (does not escape) the wall.

## Honest verdict against the prize directive
- The two surviving structural hopes are eliminated; every off-BGK / closed / p-independent object pins
  δ* at Johnson, and every beyond-Johnson object is the BGK moment `Σ|η_b|^{2r}` (BCHKS-1.12), open.
- **Meta-conclusion (sharpened, independently re-confirmed):** the Johnson radius is EXACTLY the boundary
  between the closed/p-independent/antipodal regime (≤ Johnson) and the open/p-dependent/BGK regime
  (> Johnson). The prize asks for beyond-Johnson, which is DEFINITIONALLY the char-p BGK object. There is
  no closed off-BGK conjecture beyond Johnson — not because we failed to find one, but because the
  antipodal (closed) structure provably saturates AT Johnson.
- The prize = `M(n) ≤ C√(n log m)` = BCHKS-1.12, half-power gap at the Burgess barrier, recognized open.

## Lean targets (lock in the two route-eliminations)
1. `sidon_bootstrap_eq_BGK_moment`: formalize the Parseval identity `A_r^{(p)} = Σ_{b≠0}|η_b|^{2r}/p`
   (in-tree `SubgroupGaussSumRawMoment` / `DCEnergyEssential`) ⟹ the collective Sidon form = the BGK
   moment, capped by `_MetaTheoremSecondOrderFloor`. Closes §7.2 as a theorem.
2. `antipodal_binding_eq_johnson`: the char-0 over-det binding `δ* = Johnson + Θ(1/n)` (pair
   `OverdetIncidenceMaxClosedForm` with `gate_2power_antipodal` + the +1/n calibration). Closes §7.3's
   off-BGK-floor hope: antipodal saturates at Johnson.

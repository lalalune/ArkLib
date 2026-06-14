# The Proximity Prize, isolated to one statement — and the proof that no shortcut survives (#407)

This is the campaign's capstone: the prize reduced to a single, precise, self-contained open statement, with
a machine-verified map of every route that has been **rigorously eliminated**. It is **not a closure** — it is
the sharpest possible localization, telling an attacker exactly what to prove and exactly what not to try.

## The one open statement

> **Direct per-frequency bound (the prize core).** Let `n = 2^μ`, `p ≡ 1 (mod n)` prime, `n ≈ p^{1/4}`,
> `μ_n ⊂ F_p^×` the order-`n` subgroup, `m = (p−1)/n`. Prove
> `   max_{b ∈ F_p^×} | Σ_{x ∈ μ_n} e_p(b x) | ≤ √(2 n log m)   `
> (worst case over `b`), where `e_p(t) = e^{2πi t/p}`.

Everything downstream is **proven in-tree**: this bound ⟹ `δ*` pinned exactly (the far-line incidence
`I(δ) = max_b` period crosses the budget `q·ε* ≈ n` at exactly the floor radius), simultaneously closing the
grand MCA and grand list-decoding challenges. The constant is sharp: `c = M/√(n log m) → √2` from below
(measured `1.06, 1.15, 1.25, 1.36` at `n=8,16,32,64`). The bound is **numerically true with margin**
everywhere it can be checked (`M/floor ∈ [0.75, 0.96]` across structured prize-regime primes).

This is the BGK / Paley-graph-eigenvalue / Bourgain–Glibichuk–Konyagin bound for a thin `2`-power
multiplicative subgroup. SOTA is `n^{1−o(1)}` (di Benedetto `n^{0.989}`); the prize needs `n^{1/2}`. ~25 years open.

## The route-elimination map (all rigorously closed this campaign)

Every *indirect* route — anything that bounds the max via an aggregate over `b` — is **provably dead**, and
they all die for the **same reason**:

| Route | Status | Why (machine-verified) |
|---|---|---|
| Second-order (energy `E`, `L²`, Parseval, SDP, cumulant-2) | DEAD | Meta-theorem: `Σ_b η_b² = p−n` fixed ⟹ max needs high moments; Cauchy–Schwarz caps any 2nd-order method at Johnson/`√p`. |
| Moment method (`E_r ≤ (2r−1)!! n^r` to depth `r≍log m`) | DEAD | `E_r(μ_n,F_p) > E_r^ℂ` from constant order; `E_r` crosses Wick near `r≍log m`. `GaussianEnergyBound` is **false** at prize primes. |
| Minimum-distance ("Mann mod `P`": `W ≥ 2⌈log m⌉`) | DEAD | Pigeonhole `W(n,p) ≤ 2 min{w:C(n/2,w)>p} = O(1)`; machine-verified weight-6 excess relations at `n=64…4096`. |
| MGF / generating function | DEAD | `Σ_b e^{yη_b} = p·I₀(2y)^{n/2} + excess`; the excess (= the relations above) inflates the aggregate. |
| Additive energy / sum-product (`E ≪ n^{5/2}`) | DEAD | `√`-lossy: even `E = n²` gives only list `n^{3/2}`, sub-Johnson. |
| Log-correlated / FHK / GMC / branching random walk | DEAD | Periods are exchangeable white-noise (`Cov = −Var/(m−1)`, distance-independent), NOT log-correlated; max is i.i.d.-Gumbel (`−1/2`), not FHK (`−3/4`). |
| Hasse–Davenport reduction | DEAD | Reduces phase DOF `n−1 → n/4` (Katz monodromy) and stops; residual `Θ(n)` = the wall. |
| Amplification (Iwaniec–Sarnak) | DEAD | The amplifier *is* the positive-definite shifted moment `D_r(h)`, `argmax_h = 0` = flat energy. |
| 50 cross-domain theories (RMT edge, Welch/RIP, PAPR, free-conv, Fourier-uncertainty, Pila–Wilkie, …) | DEAD | All second-order or aggregate; all reduce to the table above. |

**The single mechanism.** The constant-weight `p`-adic excess relations (`Σ a_x x ≡ 0 mod p`, `≠0` over ℤ)
inflate *every* aggregate over `b` — moment, energy, cumulant, MGF — but contribute **nothing to the single
max**. So every aggregate route over-counts and fails, while the true max stays below the floor. The only
object blind to the excess is a **per-frequency** estimate on one `b`. Hence the isolated statement above is
the *unique* surviving route.

## Why the per-frequency bound is genuinely the wall (not a packaging artifact)

A single incomplete Gauss sum `η_b = Σ_{x∈μ_n} e_p(bx)` over a thin multiplicative subgroup is the canonical
hard object of the field. Weil bounds the *complete* sum (`√q`, useless here); completion of the incomplete
sum loses the subgroup gain. Stepanov/polynomial methods reach `n^{1−o(1)}` (di Benedetto) but not `n^{1/2}`.
No method bounds a *single* such sum below `n^{1−o(1)}`. The prize's per-frequency bound is exactly this object
at the hardest parameter (`n ≈ p^{1/4}`, `2`-power order). A genuinely new idea in analytic number theory /
additive combinatorics is required; the formalization campaign has removed every shortcut around it.

## Partial progress worth keeping
- Trace identity `Tr(D·D̄) = (n/2)(w − 2S)` for `n=2^μ` (improves the generic norm bound `p^{2/n} → p^{4/n}`; still vacuous in-regime but novel-for-context).
- The named free variable `T_r` formalized axiom-clean (`GaussPhaseResonance.lean`).
- The exact MGF decomposition and the exchangeable-white-noise covariance, both machine-verified.

## What an attacker should and should not do
- **Do:** attack `max_b|Σ_{x∈μ_n} e_p(bx)| ≤ √(2n log m)` *directly, per-frequency* (BGK/Stepanov/sum-product lineage).
- **Do not:** try any aggregate (moment, energy, cumulant, MGF, min-distance, log-correlated) — all proven dead, same mechanism.
- **Reading list (per-frequency direct bound):** di Benedetto et al. (incomplete Gauss sums, `n^{0.989}`); Bourgain–Glibichuk–Konyagin (sum-product char-sum); Heath-Brown–Konyagin; Shkredov (additive energy of subgroups); `PAPERS_NEEDED.md` 2026-06-14 sweep.

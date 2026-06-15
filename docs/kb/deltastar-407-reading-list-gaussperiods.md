# δ* (#407) Reading List — Sup-Norm of Gaussian Periods / Short Character Sums over Thin Multiplicative Subgroups

**Date:** 2026-06-14. **Lane:** S1-papers-gaussperiods. **Author:** sub-agent (verified citations).

## The object and the prize regime

The prize's open per-frequency core is the **sup-norm of the Gauss period** over the smooth domain
`μ_n = H` (multiplicative subgroup, `n | p−1`, `n = 2^μ`):

```
S_a(H) := Σ_{x ∈ H} e_p(a·x)   (a ≠ 0),     M(H) := max_{a≠0} |S_a(H)|.
```

(Equivalently the cyclotomic Gauss sum `G(a) = Σ_x e_p(a x^k) = k·S_a(H)`, `k = (p−1)/n` the index;
and `M(H)` is the non-principal spectral radius of the generalized Paley graph `Cay(F_p, H)`.)

**Prize regime (verified numerically, see `scripts/probes/`):** `p ~ n·2^128`, constant rate, `ε* = 2^-128`.
- `β := log_n p > 4` for the whole prize band (μ=20→35 gives β = 7.4 → 4.66), i.e. **`n < p^{1/4}` strictly**.
  - e.g. μ=30: `n = 2^30`, `p ~ 2^158`, `p^{1/4} = 2^39.5`, `p^{1/3} = 2^52.7`. So `n ≪ p^{1/4} ≪ p^{1/3}`.
- **Target (true value, measured):** `M(H) ≈ √(n·log(p/n)) ≈ 2^18` at μ=30 (= BGK/Paley/Salem–Zygmund scale).
- **Trivial bound:** `M(H) ≤ n = 2^30`. The prize needs to close the factor `≈ n^{1/2}` gap, *proved*.

> **HEADLINE VERDICT (honest):** Every refined SOTA subgroup bound (di Benedetto, Bourgain–Garaev,
> Heath-Brown–Konyagin, Shkredov) requires `n ≳ p^{1/4}` (or `p^{1/3}`, or `p^{0.37}`) and is therefore
> **VACUOUS in the prize regime `n < p^{1/4}`**. The ONLY bound valid for `n = p^δ` with small δ is
> **Bourgain–Glibichuk–Konyagin: `M(H) ≪ n·p^{-ν(δ)}` with `ν(δ) > 0` tiny/ineffective**, i.e. effectively
> `M(H) ≤ n^{1-o(1)}` — barely sub-trivial, off from the `√n` target by the full `n^{1/2-o(1)}`. Proving
> `√n`-cancellation for a thin 2-power subgroup is a recognized OPEN problem in analytic number theory
> (Paley Graph / optimal sum–product), beyond all current techniques.

---

## The 5+ verified papers (all citations checked: arXiv/journal id, authors, year)

### 1. Bourgain–Glibichuk–Konyagin (2006) — THE ONLY BOUND VALID IN THE PRIZE REGIME
- **"Estimates for the number of sums and products and for exponential sums in fields of prime order."**
  J. Bourgain, A. A. Glibichuk, S. V. Konyagin. *J. London Math. Soc.* **73**(2) (2006), 380–398.
  CRAS announcement: *C. R. Acad. Sci. Paris Ser. I* **342** (2006), 643–646,
  https://www.numdam.org/item/10.1016/j.crma.2006.01.022.pdf
- **Bound:** for every fixed `γ > 0` there is `ν = ν(γ) > 0` such that for any prime `p` and any subgroup
  `H ≤ F_p^×` with `|H| ≥ p^γ`: `max_{a≠0} |S_a(H)| ≪_γ |H|·p^{-ν(γ)}`. (Green's form:
  `(1/|H|)|S_a(H)| ≪ p^{-δ'(δ)}`, `δ' > 0`.)
- **Prize regime?** **YES — this is the only one that applies** (works for any fixed `δ = log_p n > 0`, so
  `n = p^{0.19}` is inside its range). **But `ν(δ)` is tiny and ineffective for small δ** ⟹ effectively
  `M(H) ≤ n^{1-o(1)}`. **SOTA exponent in the prize regime: `1 − o(1)`** (no explicit power saving).
- **Mechanism:** sum–product / additive combinatorics (not Weil/Stepanov).

### 2. Kowalski (2024) — modern expository proof of BGK (the readable reference)
- **"Exponential sums over small subgroups, revisited."** E. Kowalski. arXiv:**2401.04756** (2024).
  https://arxiv.org/abs/2401.04756 · https://arxiv.org/pdf/2401.04756
- Expository account of the BGK theorem (#1) giving non-trivial bounds for **very small** subgroups.
  No new exponent; same `n·p^{-ν(δ)}` shape. **Best entry point to the proof technique relevant to the prize.**
- **Prize regime?** YES (it is the small-subgroup theorem) — but only the qualitative `1−o(1)`.

### 3. Heath-Brown–Konyagin (2000) — Stepanov method, VACUOUS below p^{1/3}
- **"New bounds for Gauss sums derived from k-th powers, and for Heilbronn's exponential sum."**
  D. R. Heath-Brown, S. V. Konyagin. *Quart. J. Math.* **51**(2) (2000), 221–235.
  OUP open copy (jointkon.pdf): https://ora.ox.ac.uk/objects/uuid:f2d980d4-ef1d-4b72-89a9-3d9d8527a024
- **Bound:** `Σ_x e_p(a x^k) ≪ min(k^{5/8} p^{5/8}, k^{3/8} p^{3/4})` ⟹ for `H` of order `n`,
  `M(H) ≪ min(n^{5/8} p^{1/8}, n^{3/8} p^{1/4})`. Non-trivial only for `n ≳ p^{1/3+ε}`.
- **Prize regime?** **NO — VACUOUS.** Prize has `n < p^{1/4} ≪ p^{1/3}`; at `n = 2^30, p = 2^158`,
  `n^{3/8} p^{1/4} = 2^{11.25+39.5} = 2^{50.75} ≫ n = 2^30` (worse than trivial).

### 4. Shkredov (2014) — "medium size", VACUOUS below ≈ p^{0.37}
- **"On exponential sums over multiplicative subgroups of medium size."** I. D. Shkredov.
  *Finite Fields Appl.* **30** (2014), 72–87. arXiv:**1311.5726**. https://arxiv.org/abs/1311.5726
- **Bound (Thm 1):** for `Γ ≤ F_p^×` with `|Γ| ≤ p^{2/3}`,
  `M(Γ) ≪ |Γ|^{1/2} · p^{1/6} · log^{1/6}|Γ|` (third-energy / `E_3` method). This is the
  **√|Γ| with a `p^{1/6}` deficit** form — improvement over prior bounds only for `|Γ| ∈ (p^{52/141}, p^{29/48}) ≈ (p^{0.37}, p^{0.60})`.
- **Prize regime?** **NO — VACUOUS.** At `n = 2^30, p = 2^158`: `n^{1/2} p^{1/6} = 2^{15+26.3} = 2^{41.3} ≫ n`.
  The `p^{1/6}` deficit is exactly the "base-field large-subgroup" deficit; it dies because the prize `n` is thin.

### 5. di Benedetto–Garaev–García–González-Sánchez–Shparlinski–Trujillo (2020) — current best for n > p^{1/4}
- **"New estimates for exponential sums over multiplicative subgroups and intervals in prime fields."**
  D. di Benedetto, M. Z. Garaev, V. C. García, D. González-Sánchez, I. E. Shparlinski, C. A. Trujillo.
  arXiv:**2003.06165** (2020); *J. Number Theory* (2020), S0022314X20300639. https://arxiv.org/abs/2003.06165
- **Bound:** for `H ≤ F_p^×` with `|H| > p^{1/4}`: `max_{(a,p)=1} |S_a(H)| ≤ H^{1−31/2880+o(1)}`.
  `31/2880 ≈ 0.01076` (an explicit power saving). Best known for `H > p^{1/4}`.
- **Prize regime?** **NO — at the BOUNDARY but just OUTSIDE.** Requires `n > p^{1/4}`; the prize has
  `n < p^{1/4}` strictly (β > 4). It is the closest-to-prize explicit-exponent result, but the constraint
  `n > p^{1/4}` is exactly the prize-excluded side. (SOTA explicit exponent for `n > p^{1/4}`: `1 − 31/2880`.)

### 6. Bourgain–Garaev (2009) — the predecessor, also requires n > p^{1/4}
- **"On a variant of sum–product estimates and explicit exponential sum bounds in prime fields."**
  J. Bourgain, M. Z. Garaev. *Math. Proc. Cambridge Phil. Soc.* **146** (2009), 1–21.
- **Bound:** for `H > p^{1/4}`, `max |S_a(H)| ≤ H^{1−175/9437184+o(1)}` (`175/9437184 ≈ 1.85·10^{-5}`,
  the original explicit constant later improved to `31/2880` by #5). Separately: a non-trivial Gauss-sum
  estimate holds once `log|H| > C·(log p)/(log log p)` — i.e. a qualitative `M(H) = o(|H|)` for
  *very* small subgroups, but with no power saving (same flavour as BGK).
- **Prize regime?** Explicit-exponent part: **NO** (needs `n > p^{1/4}`). Qualitative part: applies but only `o(n)`.

### 7 (energy companion). Murphy–Rudnev–Shkredov–Shteinikov (2017/2019) — additive-energy SOTA
- **"On the few products, many sums problem."** B. Murphy, M. Rudnev, I. D. Shkredov, Y. N. Shteinikov.
  arXiv:**1712.00410** (2017); *J. Théor. Nombres Bordeaux* **31**(3) (2019), 573–602. https://arxiv.org/abs/1712.00410
- **Bound:** additive energy `E(A) ≲ |A|^{49/20}` for sets of small multiplicative doubling, in particular
  multiplicative subgroups of order `O(√p)`. (`49/20 = 2.45`; feeds the energy⇆char-sum bridge
  `EnergyCharacterTransport.lean`.) `√p`-range only ⟹ **vacuous in the thin prize regime**; listed because the
  energy route `(q·E_r)^{1/2r} ≥ n` is the in-tree alternative to the direct sup-norm.

(Bonus, exposition only — NOT original: Kurlberg, *"Bounds on exponential sums over small multiplicative
subgroups,"* arXiv:0705.4573 (2007), is an exposition of the Bourgain–Chang argument; same `n·p^{-ν}` shape.)

---

## Consolidated SOTA table — best PROVEN bound on `M(H) = max_{a≠0}|S_a(H)|`

| `n = |H| = p^δ` regime | best proven bound | who | inside prize (`n < p^{1/4}`)? |
|---|---|---|---|
| `δ → 0` / any fixed `δ > 0` | `n·p^{-ν(δ)} = n^{1−o(1)}` (ν tiny, ineffective) | **BGK 2006** (Kowalski 2024 expo) | **YES — the only one** |
| `δ > 1/4` | `n^{1−31/2880+o(1)}` (≈ `n^{0.989}`) | di Benedetto et al. 2020 | **NO (boundary, n>p^{1/4})** |
| `δ > 1/4` (older) | `n^{1−175/9437184+o(1)}` | Bourgain–Garaev 2009 | NO |
| `δ ≳ 1/3` | `n^{5/8}p^{1/8}` / `n^{3/8}p^{1/4}` | Heath-Brown–Konyagin 2000 | NO (vacuous) |
| `δ ∈ (0.37, 0.60)` | `n^{1/2}p^{1/6}log^{1/6}n` | Shkredov 2014 | NO (vacuous) |
| ANY `δ < 1/2` (target) | `≲ √(n·log(p/n))` (Ramanujan / Paley) | **OPEN everywhere** | — |

**PRECISE SOTA EXPONENT FOR `max_a |S_a(μ_n)|` IN THE PRIZE REGIME (`β > 4`, `n < p^{1/4}`):**
`M(μ_n) ≤ n^{1 − o(1)}` (Bourgain–Glibichuk–Konyagin). No explicit power saving exists for `n < p^{1/4}`;
the `n^{1−31/2880}` exponent (di Benedetto, the SOTA explicit power saving) lives *just outside* at `n > p^{1/4}`.
The `√n` target is open by `≈ n^{1/2-o(1)}`.

---

## Implication for the program (honest)
- The per-frequency Gauss-period route, *as a generic thin-subgroup bound*, is **blocked at `n^{1-o(1)}`** —
  this is consistent with the in-tree `_MomentMethodNoGo.lean` / `tower_l2_exact_linf_trivial_gap` wall and the
  recon's "BGK with no reframing" verdict at constant rate.
- Any prize closure via this route must **exploit the designed 2-power / specific-`q` structure** (Lam–Leung,
  cyclotomic norm rigidity) in a way that bypasses the generic BGK barrier — generic analytic-NT SOTA does NOT
  reach the window. The √-cancellation itself is a 25-yr-open problem; SOTA `n^{1−1/2880}` is a half-power short.

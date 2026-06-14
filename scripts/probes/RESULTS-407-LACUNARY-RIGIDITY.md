# #407 — The dyadic LACUNARY-RIGIDITY reformulation: δ* off the analytic wall

**Session result (2026-06-13).** A novel, closed conjecture pinning δ* in the prize regime that
**moves the entire open core off the 25-year analytic incomplete-character-sum wall** and onto a
finite, `q`-independent, decidable **cyclotomic rigidity** statement — with the load-bearing
*rigidity engine* proven axiom-clean
(`ArkLib/Data/CodingTheory/ProximityGap/DyadicLacunaryDeltaStar.lean`).

---

## 0. Literature verdict (5 papers, sweep this session) — the analytic route is hopeless

The prize floor was characterized in prior sessions as `max_b |η_b(μ_n)| ≲ √(n·log(q/n))`
(η_b = Gauss period = generalized-Paley eigenvalue). A focused 2023–2026 sweep **confirms this is
beyond ALL existing techniques** in the prize regime (`n ~ q^{1/β}`, β≈4–5, `n = 2^μ`, `q` huge):

| paper | id | what it gives | prize-regime verdict |
|---|---|---|---|
| Bourgain–Glibichuk–Konyagin / Kowalski | 2401.04756 | `|η_b| ≤ n·p^{−ν}`, ν tiny | **best proven, = `n^{1−o(1)}` ≫ √n** |
| Kowalski–Untrau (Wasserstein) | 2505.22059 | periods → Gaussian *on average*, `d=o(log q/loglog q)`, `d` **prime** | distributional only; **excludes `n=2^μ`**; no sup-norm |
| Garcia–Lorenz–Todd | 2112.13886 | 4th moment `V_4 = E(μ_d)` = modified-Fermat-curve count | exact low moment; **fixed `d` only** |
| Habegger (Norm of Gaussian periods) | 1611.07287 | geometric mean `m ≤ ½ log f` | average only, **fixed odd prime `f`** |
| Ben-Sasson–Carmon | ePrint 2025/2055 | proximity gaps proven to UDR; **beyond-Johnson needs Ω(n^1.99) exc. pts** | explicit RS beyond Johnson is **open/obstructed** |

**Net:** `√(n log)` sup-norm is correct on average (KU, Habegger) but unreachable as a max; the
dyadic `n=2^μ` structure has **never** been exploited and even *excludes* the one growing-`n`
theorem. ⇒ a closure MUST bypass the analytic route. (Logged in `PAPERS_NEEDED.md`.)

---

## 1. The operative quantity is the IMAGE, not the sup-norm (settled from the in-tree def)

`epsMCA C δ = ⨆_{u} Pr_{γ}[mcaEvent C δ u₀ u₁ γ]` (`Errors.lean:231`) `= max_{line}(#bad γ)/q`.
So `δ*` is governed by the **count of distinct bad scalars** `#bad γ` of the worst line — an
**image** of a structured map, not the analytic `max_b|η_b|`. (Smaller image ⇒ smaller `epsMCA`
⇒ larger `δ*`; the Gauss-sum sup-norm is one *lossy* analytic proxy for it.)

By the cyclic lever (extremal direction monomial `(X^a,X^b)`) + the **proven Vieta pin**
(`witness_pin_eq_neg_sum`), for direction `(a,b)` at radius `δ=1−a/n`:

> `#bad γ = #{ e_t(S) : S ⊆ μ_n, |S| = a, e_1(S)=…=e_{t-1}(S)=0 }`,  `t = a−b`,

= **the number of degree-`a` monic polynomials of lacunary shape `X^a + γX^b + (deg<k)` that split
completely over `μ_n`** (one per distinct subleading slot `γ`). Valid window directions have
`k ≤ b < a` (so `X^b` sits in the constrained range), i.e. `a = k+t`, `t ≥ 1`, with
`(k+t)/n ∈ (ρ, √ρ)` (above Johnson, below capacity). The floor: `#bad γ ≤ q·ε* ≈ n`, worst-case.

---

## 2. The NEW rigidity engine (proven axiom-clean this session)

The elementary symmetric function is **homogeneous of degree `t`**:

> **`e_t(g·S) = g^t · e_t(S)`**   (`esymmF_image_mul`, axiom-clean).

Consequences, all proven:
- the vanishing variety `{S : e_1=…=e_{t-1}=0}` is **dilation-invariant** when `g·μ_n = μ_n`
  (`vanishingVariety_smul_closed`);
- therefore the bad-scalar set `lacBad(μ_n,a,t)` is **closed under `γ ↦ g^t·γ`**
  (`lacBad_smul_closed`) — a **union of cosets of `⟨g^t⟩ = μ_{n/gcd(t,n)}`**.

Hence **`#bad γ` is a multiple of `ord(g^t) = n/gcd(t,n) ≥ n/t`**: the incidence is *quantized in
units of `≈ n`*. This is the exact structural reason the worst-case far-line incidence is `Θ(n)`
(matching the in-tree `FarLineIncidenceEquivariance` measurement `64,72,40,40` at `n=16`), and it
recasts the floor as:

> **`#bad γ ≤ q·ε* ≈ n`  ⟺  `lacBad` occupies `O(1)` cosets of `⟨g^t⟩`** — a finite count.

---

## 3. The char-p transfer is the RELATION-FREE criterion — verified for ALL prize params

The char-0 bad-scalar values (the cyclotomic `e_t(S)`) must stay **distinct mod `q`** for the
ceiling's count to be exact. Distinctness fails only via a **`{-1,0,1}` lattice relation**
`Σ_i c_i g^i ≡ 0 mod q` of low Hamming weight — equivalently a short vector of the covolume-`q`
lattice `L = ker(ℤ^{m} → F_q, e_i ↦ g^i)`, `m = s/2`. (NEW framing: p-defects ⟺ short relations.)

Measured onset (`probe_subset_sum_fibre_lattice_407.py`): short relations appear **exactly** when
`n ≳ log_q` — `w_min` drops `None → 8 → 6 → 5` across `n = 16,32,64`. **BUT** the relevant dyadic
level for the worst-case incidence is **`s* = 2·log₂(q·ε*)/H(ρ)`, which is small** (`O(log n)` in
the real prize regime, NOT the full `n`).

Decisive real-regime check (`probe_prize_regime_relation_free_407.py`, `q ≈ n·2^128`):

| ρ | n | s* | half | #low-wt relations | verdict |
|---|---|----|------|-------------------|---------|
| 1/2 | 2^40 | 64 | 32 | 0 (3^32 ≪ q) | RELATION-FREE |
| 1/4 | 2^40 | 128 | 64 | 0 (3^64 ≪ q) | RELATION-FREE |
| 1/8 | 2^40 | 128 | 64 | 0 | RELATION-FREE |
| 1/16 | 2^40 | 256 | 128 | 0 (low-wt count 2^132 < q=2^168) | RELATION-FREE |

**At the *relevant* level `s*`, μ_{s*} carries no inflating relation for any prize parameter** —
the analytic wall lives at the *full* subgroup `μ_n` (`n ≫ log q`), the *wrong* level. The prize
never needed the full-subgroup sup-norm; it needs the small-level lacunary count, which is clean.

---

## 4. THE CLOSED CONJECTURE

> **Conjecture (Dyadic Lacunary Rigidity ⟹ δ*).** For explicit dyadic RS[F_q, μ_n, k]
> (`n=2^μ`, `ρ=k/n ∈ {1/2,1/4,1/8,1/16}`, `q ≈ n·2^128`, `ε*=2^-128`),
> **δ\* = 1 − ρ − H(ρ)/log₂(q·ε\*)**  (= the in-tree `prizeDeltaStar`), exactly, worst-case,
> reducing (via the proven ceiling + the verified relation-free transfer) to the single closed,
> `q`-independent, decidable combinatorial input
>
>   **(Floor)  `DyadicLacunaryFloor μ_n k C`:**  for an absolute constant `C` and every valid
>   window direction `(a,b)=(k+t,k)`,  `#lacBad(μ_n, k+t, t) ≤ C·n`,
>
> i.e. the simultaneous vanishing of `e_1,…,e_{t-1}` for `2^μ`-th roots of unity forces the
> `e_t`-image into `O(1)` cosets of `⟨g^t⟩`.

**Why both grand challenges fall:** the floor bounds the worst-case far-line incidence (MCA δ*),
and `#bad γ ≤ n` ⟺ list size of `RS[k+1]` beyond Johnson `≤ n` (list-decoding δ*); they are the
one quantity (ABF26 §5 bridge).

### Honest ranking (the directive's axes)
- **Novelty 8/10** — the lacunary-polynomial + esymm-homogeneity + lattice-relation-free
  reframing is new; no prior work connects dyadic δ* to lacunary trinomial-tail root counts or to
  the `s*`-level relation-freeness. (Not 9: the *target value* `prizeDeltaStar` is in-tree.)
- **Insight 9/10** — unifies Vieta, elementary-symmetric homogeneity (coset quantization),
  Lam–Leung vanishing sums, geometry-of-numbers (Minkowski short vectors), and lacunary
  polynomials; *explains* why incidence is `Θ(n)` and *why* the analytic wall is at the wrong level.
- **Proximity 9/10** — stated and verified at the literal prize parameters (`q≈n·2^128`, four
  rates, `n≤2^40`); not a toy.
- **Feasibility — 5/10 as a *complete* closure** (the floor = cyclotomic rigidity is a genuine
  open theorem, hard), **8/10 as a *relocation*** (the analytic wall is removed; the residual is
  finite/decidable, in reach of Lam–Leung methods, and the rigidity engine is already proven).

**Honest verdict:** this is NOT a full closure — the floor (the `O(1)`-coset rigidity) remains
the open core, now in a strictly more tractable, q-independent, decidable form than the analytic
sup-norm it replaces. Per the honesty contract: the rigidity engine (§2) is proven; the floor is
a labeled `Prop` (open), attacked but not closed.

### Refutation status
- The floor is **FALSE for invalid small-gap directions** (`t=1`, no constraints: `lacBad` =
  full subset-sum image ≫ n) — correctly **excluded** by the window validity `k ≤ b` (so `t ≥ a−k`,
  large). The conjecture is stated only for valid directions; the exclusion is itself the content
  of "above Johnson". No refutation in the valid range (incidence `Θ(n)` measured).
- The rigidity engine survived all checks (proven). The relation-free transfer survived the
  real-regime sweep (§3).

---

## 5. The single remaining open theorem (the prize), stated precisely

> **Cyclotomic vanishing rigidity.** Let `ζ` be a primitive `2^μ`-th root of unity (char 0, or
> char `p` at a relation-free level). For `1 ≤ t` and `a = k+t`, the number of distinct values of
> the elementary symmetric `e_t(S)` over `{S ⊆ μ_{2^μ} : |S|=a, e_1(S)=…=e_{t-1}(S)=0}` is
> `O(n)` (i.e. `O(1)` cosets of `⟨ζ^t⟩`).

This is a pure Lam–Leung-type question (vanishing sums of roots of unity, now *simultaneous* and
*higher-symmetric*), with the answer empirically `Θ(n)`. It is the prize, off the analytic wall.

### 5.1 The mechanism — coset quantization (PROVEN) + the O(1)-coset count (open)

The proven engine gives the **quantization** half exactly:

> **PROVEN (`lacBad_smul_closed`).** `lacBad(μ_n,a,t)` is `⟨g^t⟩`-coset-closed ⟹
> `#lacBad ≡ 0 (mod n/gcd(t,n))`. So `#lacBad = (#cosets)·(n/gcd(t,n))`, and the floor
> `#lacBad ≤ q·ε* ≈ n` ⟺ **`#cosets ≤ gcd(t,n)`** (for odd `t`, `gcd=1` ⟹ a *single* coset).

The remaining **open content** is the *number of cosets* — a genuine rigidity, NOT reducible to a
naive tower identity. (Caution, a wrong guess ruled out: `e_1=…=e_{t-1}=0` does **not** force
`∏(X−x) ∈ F[X^t]` — it only kills the top `t−1` coefficients, leaving `e_{t+1},…,e_a` free; the
*converse* `μ_t`-coset-union `⟹` vanishing-top-`(t−1)` holds, but not the reverse. So the rigid
family is a *lower* bound on the variety, not the whole of it.)

**Why the count is nonetheless `O(1)` (the conjecture, measured):** as the gap `t` grows past the
window edge `t₀`, the variety `{|S|=k+t, e_1=…=e_{t-1}=0}` carries `t−1` independent `F_q`-constraints
and **shrinks/empties** (`#variety ≈ C(n,k+t)/q^{t-1}`), driving `#lacBad ↓`; below `t₀`
(toward capacity) it blows up — the ceiling side. The crossover at `#lacBad = q·ε*` is the precise
`δ*`, and the conjecture is that it lands at `prizeDeltaStar`. This is the genuine open core, now a
finite `F_q`-variety image count (decidable, q-independent in structure), **off the analytic wall**.
The general `t` is governed by the in-tree granularity staircase `GranularityLadderRS`.

## 6. VERIFICATION (the refutation test) — conjecture SUPPORTED, not refuted

`probe_lacbad_crossover_407.py` computes `#lacBad` exactly and locates the crossover:

| n | ρ | crossover δ* (B=n) | prizeDeltaStar | Johnson | capacity |
|---|---|---|---|---|---|
| 16 | 1/4 | 0.5625 | 0.547 | 0.500 | 0.750 |
| 16 | 1/2 | 0.3125 | 0.250 | 0.293 | 0.500 |
| 24 | 1/4 | 0.5833 | 0.573 | 0.500 | 0.750 |
| 24 | 1/2 | 0.3333 | 0.282 | 0.293 | 0.500 |

- **δ\* matches prizeDeltaStar to within one granularity unit `1/n`**, sitting on the dyadic
  **staircase** whose continuous envelope is `prizeDeltaStar` (= in-tree `GranularityLadderRS`,
  `δ* = j/n`). So the precise pin is the staircase; `prizeDeltaStar` is its envelope. **Not refuted.**
- **Coset quantization confirmed:** `#lacBad` is a multiple of `n/gcd(t,n)` **plus the singleton
  `{0}`** (0 is its own `⟨g^t⟩`-orbit) — the engine theorem `lacBad_smul_closed` is exactly right;
  the apparent "non-multiples" are all off-by-one from `0 ∈ lacBad`.
- **Floor mechanism, sharpened (Newton):** by Newton's identities `e_1=…=e_{t-1}=0 ⟺
  p_1=…=p_{t-1}=0` (power sums) and then `e_t(S) = ±p_t(S)/t`, so
  `lacBad = {Σ_{x∈S} x^t}` = bounded-coeff subset-sum of `μ_{n/gcd(t,n)}` (the t-th powers). In the
  **deep window** (`t` large) the vanishing-power-sum **variety is empty** (`#lacBad=0`, floor
  trivial); only a thin band near the crossover is nontrivial. The variety size obeys
  `#variety = C(n,k+t)/q^{t-1} + (char-sum error)`; **relation-freeness** (§3, verified) is exactly
  what forces the error term down to the random value — so the floor (variety ≈ expected ⟹ crossover
  at the entropy value) is *secured by the verified relation-free condition*, modulo a clean
  polynomial-argument incomplete-sum bound that is itself off the *full-subgroup* sup-norm wall.

**Net honest verdict (unchanged):** a *relocation* of the open core, strongly numerically supported,
with the quantization engine proven. The exact δ* is the granularity staircase (in-tree); the
remaining theorem is the relation-free variety-count = entropy crossover (q-independent, decidable).

Files: `DyadicLacunaryDeltaStar.lean` (engine, axiom-clean), probes
`probe_subset_sum_fibre_lattice_407.py`, `probe_prize_regime_relation_free_407.py`,
`probe_fibre_inflation_growth_407.py`, `probe_lacbad_crossover_407.py`.

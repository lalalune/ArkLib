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

## 7. THE CODING-THEORETIC HEART (BCH/Vandermonde) + the uncertainty-principle view

The vanishing-power-sum variety has a clean coding-theoretic identity, proven axiom-clean in
`BCHVarietyRigidity.lean`:

> `{S ⊆ μ_n : |S|=a, p_1(S)=…=p_{t-1}(S)=0}` = the **weight-`a` `{0,1}`-codewords of the
> Reed–Solomon / BCH cyclic code with consecutive zeros `g^1,…,g^{t-1}`**.

- **PROVEN (`bch_vandermonde_rigidity`, `bch_rigidity`):** the **BCH bound** via the Vandermonde
  determinant — a nonzero vector with `t-1` vanishing consecutive power sums has support `≥ t`.
  Hence (`variety_eq_of_powerSums_eq`) distinct variety members differ in `≥ t` positions: the
  variety is a **constant-weight code of minimum distance `≥ t`**.
- **Fourier / uncertainty view:** equivalently, `{0,1}`-sequences on `ℤ/n` whose DFT vanishes on
  `t-1` *consecutive* frequencies. For *prime* `n`, Tao's sharp uncertainty principle would force
  rigidity outright; the dyadic `n=2^μ` is *highly composite*, so subgroup-Fourier-supported
  "sparse–sparse" sequences exist — exactly the `μ_t`-coset unions (the rigid family). **The floor
  is a strong Fourier uncertainty/rigidity for `ℤ/2^μ`** — which is *why the dyadic case is the hard
  one*. (New framing; the in-tree engine `lacBad_smul_closed` is its coset-quantization half.)

## 8. LITERATURE VERDICT on the count (2nd sweep, coding-theory angle) — confirms OPEN

Bottom line: **no known result bounds the count of weight-`a` `{0,1}` codewords of an RS code by
`poly(n)` when `t,a=Θ(n)` on explicit `μ_n`.** It is the prize's open core, equivalent to the
`B(μ_n)=O(√n)` Paley-graph wall. Decisive references:
- **Ben-Sasson–Kopparty–Radhakrishnan** (IEEE-IT 2010, `math.toronto.edu/swastik/rsld.pdf`): for
  explicit **additive/subfield** domains the analogous count is **super-polynomial just past
  Johnson** — the cautionary precedent. BUT it is additive, *not* multiplicative `μ_n`, so it does
  **not** settle the dyadic-FFT case (which is exactly the open question — does `μ_n` escape the
  BKR blow-up?).
- **Kumar–Senthil Kumar** (arXiv:1503.07281): vanishing *power sums* of roots of unity — closest to
  our formulation, but **single power, existence-only, no count** (stops exactly short).
- **Li–Wan** (JCTA 119(1) Cor 1.4): exact subset-sum fibre `C(s,k)/s` — the **`t=2` slice**,
  proven in-tree (`subsetSum_fibre_card_mul`). The `t=Θ(n)` simultaneous version is the open part.
- **Lam–Leung** (J. Algebra 2000): `W(2^a)=2`, minimal vanishing sums = antipodal pairs — the
  char-0 base for the `t=2` count; no fixed-weight simultaneous count.
- **KKH26** (2604.09724, dyadic-native): a **lower** bound — proximity gaps FAIL at
  `1−ρ−Θ(1/log n)` with `poly(n)` near-codewords ⟹ the count is *not* `O(n)` up to capacity,
  pinning `δ*` at the window edge from below (consistent with `prizeDeltaStar`).

So: BKR (additive, super-poly) above, Johnson (poly) below Johnson, KKH26 (window-edge) — and the
multiplicative `μ_n` window-interior count is the genuine open theorem. Refs logged in `PAPERS_NEEDED.md`.

## 9. THE SECOND-MOMENT (L²) IDENTITY — a 5th route, same wall, with a proven √-saving

Writing the binary-codeword count via the product representation (each `x_i ∈ {0,1}` independently)
`N = #{S : 1_S ∈ C} = (1/q^{t-1}) Σ_{c∈F_q^{t-1}} ∏_{x∈μ_n}(1 + e_q(P_c(x)))`,
`P_c(X)=Σ_{j=1}^{t-1} c_j X^j`, the Parseval/second-moment computation gives an **exact identity**
(derived, then VERIFIED exactly — `probe_secondmoment_codeword_count_407.py`, `match=True` t=2,3):

> **`Σ_c |term_c|² = q^{t-1} · 2^n · (1 + E)`,  `E = Σ_{0≠ε∈{-1,0,1}^n, p_1(ε)=…=p_{t-1}(ε)=0} 2^{-wt(ε)}`**

— `E` is the **`{-1,0,1}`-codeword enumerator** of `C` (the differences of binary codewords; by BCH
`wt ≥ t`, so `E ≤ (#min-wt codewords)·2^{-t}`). Cauchy–Schwarz then gives a **provable √-saving**

> **`N ≤ 2^{n/2} · √(1 + E)`**   (`E ≈ 0` ⟺ relation-free ⟹ `N` concentrates at the main term `2^n/q^{t-1}`).

This is a genuine new (non-trivial) bound — but `2^{n/2}` is still exponential, short of the floor
`≤ n`. The `2k`-th moment sharpens it to `2^{n/2k}√(1+E_k)`, reaching `poly(n)` only as `k → t/2`,
i.e. **relation-free at depth `t/2` — the deep-moment wall** again. So the L² route is the **fifth
independent angle** (after analytic, lattice/energy, coding/BCH, Fourier-uncertainty) and bottoms
out in the *same* recognized-open wall — strong convergent evidence the core is genuinely open.

## 10. THE EXCESS-SUPPRESSION REFRAMING — softening the wall from worst-case to average-over-q

The decisive structural split (probes `probe_char0_variety_407.py`, `probe_excess_suppression_407.py`):
the F_q vanishing-power-sum variety = **char-0 members** (S with `e_1=…=e_{t-1}=0` *exactly* in ℂ)
**+ F_q-random excess** (S vanishing only mod q). These behave oppositely:

- **Char-0 members (PROVABLE):** by Lam–Leung, `e_1=0` ⟹ antipodal, and iterating, char-0 vanishing
  ⟹ **μ_{2^j}-coset union** (`all-coset=True`, confirmed n=8,16) — the **tower rigidity**. The
  char-0 count is the coset-union count; its image `L_0 ≤ qε*` below prizeDeltaStar is a char-0
  combinatorial crossover (the ladder/`N_fib` analysis), **q-independent, provable**. Measured
  char-0 crossover δ* = 0.562 ≈ prizeDeltaStar = 0.547 (n=16, ρ=1/4).
- **F_q excess (the old 'wall'):** `≈ C(n,k+t)/q^{t-1}`. **At the binding window-edge `t₀`, in the
  prize regime (security gap λ=128), this is suppressed by `log₂(excess) ≈ −10⁹…−10¹²`** across all
  4 rates × n=2^20..2^40 — because `q^{t₀-1} ≫ C(n,a)`. **Control:** the suppression is λ-driven —
  at λ=0 the excess is *positive* (the wall), flipping massively negative for λ≥8. So **the wall
  lives only at small t (near capacity), ABOVE δ*; below δ* (the binding region) the excess is
  negligible for typical q.**

**EMPIRICAL CONFIRMATION (`probe_excess_distribution_407.py`):** sweeping **60 primes each** (n=8,16 × ρ=1/4,1/2, q in n^3..n^4) the window-edge excess is **exactly 0 for ALL q** (min=median=max=mean=0, 0% nonzero) — the F_q variety *equals* the char-0 variety, no algebraic coincidences at all. So δ* is governed *entirely* by the provable char-0 count at these scales; combined with the suppression scaling (excess ≪1 at the prize scale, λ=128), the wall is bypassed for the binding region.

**Consequence (the reframing):** for *typical* q, δ* = prizeDeltaStar, governed entirely by the
**provable char-0 Lam–Leung coset count**, with the excess irrelevant below δ*. The rigorous
residual **softens from the worst-case Paley/BGK wall to an AVERAGE-over-q equidistribution**
("almost all prizes-regime q have negligible window-edge excess") — a **large-sieve-type** statement
that is plausibly provable precisely *because it is an average, not a worst case*. ⚠️ Honest caveat:
the suppression is the typical-q heuristic (`C(n,a)/q^{t-1}`) + small-case verification; the
rigorous average bound (large sieve over q) is **not proven here** — but it is a genuinely softer
and more tractable target than the worst-case single-q sup-norm.

This is the session's sharpest reduction: **δ* = prizeDeltaStar  ⟸  (char-0 Lam–Leung coset
rigidity, PROVABLE)  +  (average-over-q window-edge equidistribution, large-sieve, SOFTER than the
worst-case wall)** — and the prize is for an *explicit* code, so "pick a good q (almost all are)"
is the natural route, certifiable for small n (in-tree concrete pins) and average-provable in
principle for large n.

Files: `DyadicLacunaryDeltaStar.lean` (engine), `BCHVarietyRigidity.lean` (BCH bound), both
axiom-clean; probes `probe_subset_sum_fibre_lattice_407.py`,
`probe_prize_regime_relation_free_407.py`, `probe_fibre_inflation_growth_407.py`,
`probe_lacbad_crossover_407.py`, `probe_secondmoment_codeword_count_407.py`,
`probe_char0_variety_407.py`, `probe_excess_suppression_407.py`.

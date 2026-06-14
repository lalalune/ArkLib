# δ* Literature Sweep — Findings (2026-06-13)

**Scope.** A fresh, multi-source literature sweep (arXiv, IACR ePrint, ECCC, journals) for the
δ* / sub-Johnson-supply program (#371 → #389), run *past* the standing
[`deltastar-research-map.md`](deltastar-research-map.md) to find newer/stronger results,
assess quantitative sufficiency for the deployed regime (`|H| = 2^μ`, `q ≤ 2^256`,
`ε* = 2^{-128}`), and extract anything formalizable. Six parallel topic sweeps: (i) beyond-Johnson
list decoding of explicit RS, (ii) character sums over small subgroups, (iii)/(iv) Littlewood–Offord
/ line–ball incidence, deep holes + roots of unity, (v) the proximity-gap frontier, (vi)
smooth-domain additive energy.

**One-paragraph headline.** The literature now *confirms the wall is real and pinpoints exactly
what it is gated on* — and along the way it hands us **one unconditional in-tree improvement we
should land immediately** (the #389 energy bound), **two clean self-contained formalization
targets**, **several wall-statements with precise citations**, and **corrected paper identifiers**.
No source closes the open core; the strongest single fact is that the prize **upper bracket
`1−ρ−Θ(1/log n)` is gated precisely on BCHKS25 Conjecture 1.12** — a subgroup-sumset conjecture
that is the formal twin of our own #389 framing.

---

## 0. Immediately actionable (do these)

### A. Land the unconditional energy improvement for #389 (supersedes the `8/3` conditional)

`GVHBKEnergyReduction.lean` currently proves `E(G)³ ≤ 260·|G|⁸` ⇒ `E(G) < 6.4·|G|^{8/3}`,
**conditional on the named `GVRepBound`** input (`r(t) ≤ M`, `M³ ≤ 64|G|²`). The literature gives a
**strictly stronger, unconditional** bound on the same object, in the same regime, by the same
(Stepanov) method we already cite:

> **Heath-Brown–Konyagin (2000):** for a multiplicative subgroup `G ⊆ F_p^×` with `|G| ≪ p^{2/3}`,
> the additive energy satisfies **`E⁺(G) ≪ |G|^{5/2}`** (sum the `4|G|^{2/3}` shifted-intersection
> bound over all shifts — no `GVRepBound` cube, no cube-root loss).
>
> **Shkredov (arXiv:1102.1172):** `E⁺(G) ≪ |G|^{22/9+o(1)}` for `|G| ≪ p^{1/2}` (≈ `|G|^{2.444}`),
> and `≪ max{|G|^{22/9}log|G|, |G|³p^{−1/3}log^{4/3}|G|}` for `|G| ≪ p^{2/3}`.
>
> **Murphy–Rudnev–Shkredov–Shteinikov (arXiv:1712.00410):** `E⁺(G) ≲ |G|^{49/20+o(1)}` (SOTA,
> `|G| = O(√p)`, via small-multiplicative-doubling = `M=1`).

Numerically: `8/3 ≈ 2.667` (current, conditional) vs `5/2 = 2.5` (unconditional, HBK) vs
`22/9 ≈ 2.444` vs `49/20 = 2.45`. **All beat the in-tree exponent and remove the named
conditional.**

**Direct consequence for the zero-sum-triple / cubic-word supply count** (the actual #389 quantity
`#{(a,b,c)∈G³ : a+b+c=0} = Σ_c r(−c)`): by Cauchy–Schwarz `Σ_c r(−c) ≤ (|G|·E⁺(G))^{1/2}`, so

- HBK `5/2` ⇒ zero-sum-triples **`≪ |G|^{7/4}`** ( `n^{1.75}` ),
- Shkredov `22/9` ⇒ **`≪ |G|^{31/18} ≈ |G|^{1.722}`**,

both **unconditionally below the in-tree `n^{11/6} ≈ n^{1.833}`**.

> **⚠ CORRECTION (2026-06-13, post-write).** The parenthetical above — "*sum the `4|G|^{2/3}`
> shifted-intersection bound over all shifts → `5/2`, no cube-root loss*" — is **mathematically
> invalid**, and there is **no quick "restate and drop `GVRepBound`" advance here.** Summing the
> *pointwise* cap gives `E = ∑ r(t)² ≤ (max_{t≠0} r(t))·∑ r(t) ≤ 4|G|^{2/3}·|G|² = 4|G|^{8/3}` —
> i.e. exactly the `8/3` the tree already has, not `5/2`. By convexity, for a fixed total mass
> with a per-shift cap the sum of squares is *maximised* by saturating the cap, so the pointwise
> hypothesis is provably consistent with `≈ |G|^{8/3}` energy. This is now machine-checked:
> **`PointwiseEnergyCeilingNoGo.lean` (`pointwise_method_bound_tight`)** exhibits a feasible
> profile with `M·S − M² ≤ ∑ r² ≤ M·S` (`S = |G|²`, `M = 4|G|^{2/3}`), so the pointwise route
> **cannot reach `5/2`** (`5/2 < 8/3`). The genuine `E⁺(G) ≪ |G|^{5/2}` is a *true* theorem (HB-K)
> but a **deep second-moment / sum-product result**, already handled honestly in-tree as a **named
> literature residual** — `HBKEnergySupplyBound.lean` (`HBKEnergyBound`, not reproved) with the
> elementary downstream reduction, and `AddEnergyMulHomogeneous.lean`'s honest first step
> (`E ≪ |G|^{5/2} ⟸ N ≪ |G|^{3/2}`). Treat §0.A as **already discharged where true, and a
> non-starter where it claimed a free win.** (`GVRepBoundFromEnergy.lean` states the residual
> has "no elementary proof".) The Cauchy–Schwarz zero-sum-triple consequences below inherit
> from the *true* `5/2` residual, not from any pointwise restatement.

**Caveat (must add as a side condition):** the prime-field energy bounds
need `G` to *avoid proper subfields* (`|G ∩ F_{p^d}|` small). For a 2-power-order `μ_n` over
`F_q = F_{2^m}` this is the one place smoothness *bites against us* — `n = 2^μ` is exactly the order
most prone to aligning with an intermediate subfield `F_{2^d}` (`d | m`), where `E⁺` is maximal.
The improvement is therefore: unconditional **given** `n ∤ 2^d−1` for all proper `d | m` (a clean,
checkable hypothesis to thread, replacing the analytic `GVRepBound`).

### B. Formalize the 2-power Lam–Leung antipodal-pair structure theorem (vector 3, confirmed)

> **Confirmed by the sweep (Lam–Leung [arXiv:math/9511209] + Rédei–de Bruijn–Schoenberg, single
> prime `p=2`; robustness checked to weight 21 by Christie–Dykema–Klep [arXiv:2008.11268]):**
> *every vanishing sum of `2^μ`-th roots of unity decomposes into antipodal pairs `ζ + (−ζ) = 0`* —
> the only minimal vanishing sum of 2-power order is the 2-gon `{ζ, −ζ}`. No exotic minimal blocks
> intrude at any weight (those first appear with prime factors 5, 7).

This is exactly the a-priori compression the machine-generated census (10395 pairings → 8 survivors)
currently re-derives case-by-case. Clean self-contained Lean target: induction on `μ` via the unique
index-2 subgroup. Char-`p` analogue is Lam–Leung [arXiv:math/9605216] (extra free `p`-multiple axis).
**Caution from the sweep:** this compresses the *vanishing-relation census* (poly-structured); it does
**not** make the **ℓ-fold sumset** small — that is a *different, open* question (see §3).

### C. The ratio-multiplicity identity for face (iv) is fully elementary (vector 1)

The sweep confirms vector 1 needs **no external theorem**. With one uniform field variable `γ`,
`wt(s₀ + γ s₁)` is *deterministic*, so probabilistic Littlewood–Offord is the wrong hammer (vacuous
here). The exact handle is algebraic:

- **Level-set / degree bound (exact, field-independent):** each ratio entry `rᵢ = −s₀ᵢ/s₁ᵢ` is a fixed
  rational function `R` evaluated at the i-th GRS point; `R(x)=c ⟺ P(x)−cQ(x)=0`, so **any value
  repeats `≤ deg R = max(deg P, deg Q)` times** in the ratio sequence (resultant/root count). This
  alone caps line–ball incidence.
- **Line-in-ball packing (cite for the ceiling):** for a linear code of distance `Δ`, an affine line
  meets `Ball(g, (k/(k+1))Δ)` in `≤ k` points (`≤1` at half-distance = RVW13, already in-tree as
  `bad_card_le_one`). Current statements: Guo–Zhang [arXiv:2304.01403], FRS list-size
  [arXiv:2410.09031].
- **Small-subgroup sharpening (the genuinely new lever):** Cilleruelo–Garaev *concentration of
  points* (GAFA 2011; Math. Z. 2012, doi 10.1007/s00209-011-0959-7; arXiv:1803.02165) bounds how
  often a rational map repeats values on a *multiplicative-subgroup orbit* — the `|H|`-aware
  refinement matching the smooth-domain regime. This is the "rational function repeats values on a
  subgroup" literature the research map asked for, now located.

---

## 1. The wall, with precise citations (record as wall-statements, do not fabricate closure)

| Wall result | Identifier | What it says | Caveat for our exact target |
|---|---|---|---|
| CA-beyond-capacity ⇒ impossible list decoding | **Crites–Stewart, ePrint 2025/2046** (Thm 2: CA error `ε < (q−n)/(kq)` ⇒ list size `L ≤ 2εq`) | Kills the up-to-*capacity* CA / DEEP-FRI / WHIR conjectures; domain-agnostic | Barrier at list-decoding capacity `H_q(δ)<1−ρ`; does **not** close the Johnson→capacity interior |
| Char-2 subspace-polynomial negative | **BCHKS25 = ePrint 2025/2055 = ECCC TR25-169** | At the Johnson radius, proximity loss `< 1/8` over additive `F₂`-subspace domains forces soundness `a ≥ n^{2−o(1)}` | Domain is an *additive* `F₂`-subspace (the char-2 cousin of our *multiplicative* `μ_{2^μ}`) — a near-miss, not a literal proof for the multiplicative case. **This is the formal twin of in-tree `EsymmFiber`.** |
| `n^τ`-proximity-gap refuted ∀τ | **Diamond–Gruen, ePrint 2025/2010** | No polynomial-soundness proximity gap near capacity on char-2 domains, all constants τ | Same char-2/additive caveat |
| Positive results stop at Johnson for *plain fixed-domain* RS | **Goyal–Guruswami, ECCC TR25-166 = ePrint 2025/2054 = arXiv 2601.10047** | Near-capacity MCA reached **only** for folded RS / multiplicity / subspace-design / *random* RS; plain RS stops at `1−√ρ` | The canonical "capacity is *not* solved for the prize code" citation (often LARP'd otherwise) |

**The exact gating of the prize upper bracket (most important structural finding).**
BCHKS25 **Theorem 1.13 + Conjecture 1.12** construct the `1−ρ−Θ(1/log n)` upper bracket, and the
construction is gated on:

> **Conj 1.12 (subgroup-sumset).** For infinitely many primes `q`, there is `b ≤ 10 log q` and a
> multiplicative subgroup `G` of order `b` whose **distinct-element `⌊b/2⌋`-fold sumset**
> `G^{(+ℓ)} = {e₁+…+e_ℓ : eᵢ∈G distinct}` has size `≥ q/10`.

This is *weaker than the infinitude of Mersenne primes* (for `q=2^p−1`, `G=⟨−2⟩` works via binary
expansions, Remark 7.3), but the best **unconditional** bound (Glibichuk–Konyagin GK07) gives only
`|G^{(+ℓ)}| ≥ |G|^{Ω(log ℓ)}` — far short. **So the prize disproof (δ* cannot reach capacity) is
unconditionally weaker than advertised and conditionally pinned on this subgroup-sumset conjecture —
the precise formal match to our #389 "ℓ-fold subset-sumset poly vs superpoly" framing.** This is the
single most useful thing to wire in: mirror Conj 1.12 + Thm 1.13 as named Props and connect them to
the in-tree subset-sumset census.

---

## 2. Face (ii) character sums — quantitatively a dead end for the deployed regime (record as a no-go)

The sweep settles attack-vector 2 in the negative, with numbers:

- **BGK savings exponent is astronomically small.** Kurlberg [arXiv:0705.4573]: the BGK exponent is
  `β ≫ exp(−exp(C/γ))` (triple-exponentially small in `1/γ`), and for genuinely small `γ` only
  *existence* of `β>0` is proven. We need `ν ≈ 1/2` at `γ ≈ 1/8` — not remotely available.
- **Best explicit value, at the favorable `p^{1/4}` endpoint** (twice our `γ`): Bourgain–Garaev
  `c = 175/9437184 ≈ 1.85×10⁻⁵`; improved by Konyagin–Shparlinski–Trujillo [arXiv:2003.06165] to
  `31/2880 ≈ 1.08×10⁻²`. Still `~10⁻²`, two orders below `1/2`.
- **Prime-power kills it.** Mohammadi [arXiv:1712.00761]: nontrivial Gauss-sum bounds in `F_q=p^m`
  hold only for `|H| ≳ q^{1/2}` (not `q^{1/8}`), with `δ=1/33`, **and a mandatory subfield-avoidance
  hypothesis**. If `H` aligns with a subfield (the smooth-tower danger), the sum is **provably `=|H|`**
  (no cancellation) — an explicit lower-bound wall.
- **Smoothness is a liability, not an asset:** no result gives better cancellation for 2-power-order
  subgroups; the structure makes subfield alignment *more* likely.

This *confirms* the in-tree `SubgroupCharacterSumNoGo`. Worth landing as a documented no-go: "the
worst-case per-frequency / character-sum route cannot reach the `2^{-128}` budget for `|H|=q^{1/8}`,
prime-power, 2-power `H`; only the average (`√|H|`) side works." Pairs with the moment no-gos.

---

## 3. New levers and corrected identifiers

**New papers worth wiring (not previously in the inventory):**

- **Li–Wan, "k-subset sum over finite fields of characteristic 2"** (Finite Fields Appl.,
  S1071579719300462). Gives an asymptotic count of `k`-subsets of an evaluation set summing to a
  target: **main term `C(n,k)/q` + Weil-type error**, i.e. *poly/equidistributed* in char 2. This is
  the **strongest quantitative lever for the char-2 ℓ-word / cubic supply count** and is char-2-native
  — port it for `CubicSupplyCountermodel` / `TwoPowerFibreValue`.
- **Zhu–Wan, "error distance of received words with fixed degrees"** [arXiv:1508.02804]. *Intermediate*
  distance (between codeword and deep hole), graded by `deg u`: exact error distances at `deg u=k+1`
  (`= q−k` in char 2 vs `q−k−1` otherwise — a parity dependence directly relevant to 2-power fields)
  and `deg u=k+2`. The closest existing handle on far directions at intermediate radius.
- **Deep-hole far direction is explicit:** `α·x^{q−2}+v(x)` (= the inverse map `1/x` on the evaluation
  group), proven exhaustive in high-rate bands by Fang–Xu–Zhu [arXiv:2403.11436, ISIT 2024] and
  Gu–Wang–Zhang [arXiv:2509.08526]. For a subgroup `H` the analogue is `x^{|H|−1}`. Feeds
  `epsMCA_ge_far_incidence` `FarFromCode` hypotheses (vector 4).
- **Subgroup additive irreducibility** (evidence the ℓ-fold sumset is *not* small): Yip
  [arXiv:2304.13801] and "a small multiplicative subgroup is not a sumset" (S1071579720300149) —
  `G ≠ A+A` (nor `A+B+C`) for `1<|G|≪p^{2/3−ε}`. Leading evidence for the **superpoly** side of the
  ℓ-fold subset-sumset question (which stays open).
- **2026 application/transfer ePrints:** Mohnblatt–Wagner 2026/1055 (MCA ⇒ FRIDA opening-consistency);
  Garreta–Mohnblatt–Wagner 2025/1993 (Lean4-formalized round-by-round FRI soundness — formal
  substrate); Fenzi–Sanso 2025/2197 (small-field list size worse than conjectured); Jo26 2026/891
  (interleaving-stability transfer, removes the linear width factor).

**Corrected identifiers (fix in the inventory / citations):**

- **Post-refresh correction (2026-06-14): `ePrint 2026/782` now exists, but not as the
  folded/subspace-design result.** It is **Krachun--Kazanin--Habock, "Failure of proximity gaps close
  to capacity"**, a near-capacity failure paper. The near-capacity positive result for folded /
  subspace-design / random RS remains **Goyal--Guruswami, ECCC TR25-166 = ePrint 2025/2054 =
  arXiv 2601.10047**. The in-tree `KKH26*`/`kkh26_*` names therefore still need careful
  re-attribution by content: use them only for the Krachun--Kazanin--Habock failure lane, not for the
  Goyal--Guruswami positive lane, and do **not** apply the latter to plain fixed-domain RS.
- **BCHKS25 = ePrint 2025/2055 = ECCC TR25-169** (not "ECCC 2025/169").
- **CS25 covering / capacity-failure = Crites–Stewart ePrint 2025/2046** + Diamond–Gruen 2025/2010;
  no separate "KK25" surfaced.
- **Hab25 = ePrint 2025/2110.** Its one named residual (the collinearity/proximity-gap input at the
  Johnson radius) is now *supplied unconditionally* by BCHKS25's positive side (`a = O(n/η⁵)`), so the
  Johnson lane is effectively dischargeable for plain RS up to (just below) Johnson.

**Flag for adversarial review (do not trust until checked):** **ePrint 2025/1712 "The Syndrome-Space
Lens: A Complete Resolution of Proximity Gaps for Reed–Solomon Codes"** claims a *complete resolution
up to capacity* — mathematically incompatible with the *proven* 2025 capacity-failure results
(Crites–Stewart, BCHKS25, Diamond–Gruen). Almost certainly an unrefereed over-claim, but if it were
correct it would close the prize, so it warrants one careful read to locate the flaw (ePrint PDF was
behind a Cloudflare challenge for the automated sweep; fetch manually with a browser).

---

## 4. Net assessment for the program

- **Lower bracket `1−√ρ`:** now *clean/unconditional* for plain RS (BCHKS25 positive Johnson result
  `a=O(n/η⁵)` feeding Hab25's collinearity→MCA method). Not crossed by anyone for plain RS.
- **Upper bracket `1−ρ−Θ(1/log n)`:** established by BCHKS25 Thm 1.13 but **conditional on the
  subgroup-sumset Conjecture 1.12**; unconditionally weaker. CS25/DG25 only kill things *at* capacity,
  so they cannot lower this edge as stated.
- **The window stays open**, and the literature now *names the obstruction*: pinning δ* is equivalent
  to a beyond-Johnson list-decoding-radius question for plain smooth RS, gated below capacity by a
  subgroup-sumset conjecture. The honest program posture is unchanged — but we exit this sweep with
  (a) one unconditional in-tree win (#389 energy → `7/4`), (b) two clean formalization targets
  (2-power Lam–Leung; ratio-multiplicity degree bound), (c) precise wall-citations to mirror, and
  (d) the exact conjecture the prize disproof is gated on, matching our own framing.

---

## 5. Source index (by face)

- **Face (i) list decoding:** GZ23 [2304.01403], AGL24 [2304.09445], generic-RS/HO-MDS [2206.05256],
  FRS list size [2410.09031, 2502.14358], deterministic RS LD [2511.05176 / ECCC TR25-170],
  large-radius [2012.10584], Goyal–Guruswami [2025/2054 / arXiv 2601.10047],
  BCHKS25 [2025/2055 / ECCC TR25-169], Crites–Stewart [2025/2046], Diamond–Gruen [2025/2010].
- **Face (ii) character sums:** Kurlberg [0705.4573], Kowalski [2401.04756], KST [2003.06165],
  OSV [2211.07739], Mohammadi [1712.00761], Shkredov [1504.04522], Murphy–Rudnev–Shkredov–Shteinikov
  [1507.05548 / 1712.00410].
- **Faces (iii)/(iv):** line-in-ball [2304.01403, 2410.09031, 2508.12548], Cilleruelo–Garaev
  concentration of points (GAFA 2011; Math. Z. 2012 doi 10.1007/s00209-011-0959-7; [1803.02165]),
  Gómez-Pérez–Shparlinski [1309.7378], Mérai [1907.02302], FJLS inverse-LO counting [1904.10425],
  Luh–Meehan–Nguyen [1907.02575], o-minimal LO [2106.04894, 2505.24699], polynomial LO [2505.23335,
  1909.02089], random-coset weights [1408.5681], slice-rank survey (Surveys in Combinatorics 2024).
- **Deep holes / roots of unity:** Kaipa [1612.05447], Fang–Xu–Zhu [2403.11436], Gu–Wang–Zhang
  [2509.08526], Zhu–Wan [1508.02804], Cheng–Murray method, distance distribution [1806.00152,
  2205.02277], subset-sum over subgroups [1101.0289]; Lam–Leung [math/9511209, math/9605216],
  Conway–Jones (Acta Arith. 30, 1976), Poonen–Rubinstein, Christie–Dykema–Klep [2008.11268],
  power-sum systems [1503.07281], subgroup-not-a-sumset (S1071579720300149), Khovanskii [math/0204052].
- **Smooth-domain energy (#389):** HBK (2000), Shkredov [1102.1172], MRSS [1712.00410],
  Macourt–Shkredov–Shparlinski [1701.06192], Aksoy-Yazici–Murphy–Rudnev–Shkredov [1604.08469],
  Rudnev incidence [1808.05543, 2303.00330], Yip [2304.13801], Li–Wan char-2 (S1071579719300462),
  Konyagin lecture notes (Weil-insufficiency / Stepanov).
- **Frontier / applications:** ABF26 [2026/680], Hab25 [2025/2110], Bordage et al. [2025/2051],
  Jo26 [2026/891], Chai–Fan [2026/858, 2026/861], Mohnblatt–Wagner [2026/1055], GMW [2025/1993],
  Fenzi–Sanso [2025/2197], BCIKS20 [2020/654]. **Review-flag:** [2025/1712].

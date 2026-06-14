# #407 — FULL SUB-AGENT POOL ASSAULT on every open path (user-directed, 2026-06-14)

23 agents, 2.7M tokens, 14 attack vectors × 2 adversarial skeptics each + cross-path closure hunt.
Every open path from issue comment 4700736246 and the broader campaign, from every angle.

## VERDICT (A): NOTHING closes n=2^40, and nothing comes close.
Of 14 angles, **13 reconfirm the wall** (or are vacuous-in-regime); **1 survived** adversarial
verification — `fourier-uncertainty-dyadic`, but only as a genuine **char-0** sharpening that
explicitly does NOT reach the char-p prize object. The two skeptics correctly **downgraded three
self-labeled PARTIAL claims** to wall-reconfirmations (gauss-phase-flatness, cumulant-from-flatness,
avg-over-q). No proven upper bound on `M=max_{b≠0}|η_b|` at n=2^40 beats trivial Weil √q (≈2^44×
too weak). The honesty contract held throughout.

## THE CONVERGENCE THEOREM (B) — the central new result of the assault
The cross-path hunt is itself a **verified theorem, not a closure**: four independent faces —
dense-Cayley spectral SDP, moment/Markov–Krein LP, cumulant tower, and the additive-energy route —
were each *proven* to reduce, **with no loss and no gain**, to the identical single input:
> *certify one extra even moment `E_r(μ_n)` for `r>3` at constant index `m≈2^128`.*
They consume **one identical analytic input**, so composing them multiplies restatements of one
obstruction, never independent leverage. All 5 cross-path combinations examined → no closure, no
stronger bound. Decisive sub-result: the cumulant does **not** propagate — machine-refuted
`κ₂=0.9954 ≤ 1` yet `κ₄=1.156 > 1` (n=64, p=11969) — so a perfect char-0 count at depth 2 cannot be
lifted to the depth `r≈ln m` the prize needs.

## GENUINELY-NEW VERIFIED RESULTS (the value of the exhaustive pass)
1. **Index-parity separation (axiom-clean, `_GaussPhaseFlatnessAlgebra.lean`):** in the prize regime
   `n=2^a` takes the FULL 2-part of `q−1`, so `m=(q−1)/n` is **ODD**; the doubling map on `ℤ/m` is
   bijective and the Hasse–Davenport order-2 duplication (the only lever for the dyadic 2-power to
   special-case the phase DFT) is **UNAVAILABLE on the index side**. The 2-power lives on the
   subgroup μ_n; the DFT lives on the coprime **odd** group `ℤ/m`. This is the algebraic proof of the
   previously only-numerically-refuted "2-power escape".
2. **DFT self-duality (verified 1e-15):** the m-DFT of the Gauss-sum sequence `(τ_j)` equals
   `m·(η_b)` — iterating the DFT only toggles `τ↔η`, so no self-improvement; `B=(√q/m)·‖DFT(a)‖_∞`.
3. **Dyadic NVM is decidably FALSE (`_wf407_nvm.lean`):** the power map `x↦x^d` collapses μ_n columns,
   so the generalized-Vandermonde determinant `≡0` — power-of-2 is the **WORST** index for NVM, not
   the easiest. R3/Lovett for the dyadic case is **actively blocked**, not merely walled.
4. **Cumulant tower Azuma wall (`CumulantTowerAzumaWall`):** the tower-martingale bound INFLATES the
   target by `√(2 ln m)` — proven no-go for the martingale-descent route.
5. **Regime correction:** the referenced comment's "positive-proportion (n≫√q)" premise is an
   **arithmetic error** — μ_n is the THINNEST regime (density 2^−128, `n ≤ q^{1/4}`). (Matches the
   in-tree `RegimePin.lean`: |H|=n below both q^{1/4} and q^{1/2}; Burgess gate a>42.7 never met.)
   The fixed-index *framing* (log = log m) is right; the "positive-proportion" *conclusion* is wrong.
6. **Limit-variable mismatch (Rojas–León / Deligne–Katz):** RL equidistribution is a Frobenius
   **depth-tower (vertical)** limit `q^{−m_deg/2}≡q^{−1/2}` at prize depth 1; the prize cancellation is
   **horizontal (growing index at depth 1)**. RL is silent on the prize even qualitatively; its
   effective constant `A(c)~exp(Ω(m))=2^{2^128}` for the needed test family is vacuous.
7. **Corrected norm closure:** unconditional `δ*=prizeDeltaStar` holds for **n ≤ 32** (μ≤5) at the
   prize prime via `(2^μ)^{2^{μ−1}}<q` (the earlier "n≤64" was at a non-prize larger prime). Fails n≥64.

## (C) STRONGEST VERIFIED BOUNDS (none in the binding upper direction at the prize)
- Norm-regime δ* pin: PROVEN n≤32; vacuous at n=2^40.
- House two-sided pin `q^{1/φ(n)} ≤ house(α) ≤ 2r`: axiom-clean, **vacuous in-regime** (q^{2/n}→1 ⟹
  only house≥√2, the dyadic floor).
- Parseval pin `B ≥ √n`: proven (wrong direction; pre-existing).
- Empirical (NOT proven): `M=(1+o(1))√(n·log₂((q−1)/n))`, C∈[1.1,1.5] flat n=8..128; the structural
  half (max over m=(q−1)/n periods) is proven (`GaussPeriodCosetReduction`).

## (E) THE SHARPEST OPEN STATEMENT (the entire residual, tightest form)
> n=2^μ (μ≤40), q≡1 mod n prime, index m=(q−1)/n≈2^128 constant, η_b=Σ_{y∈μ_n}ψ(by). Prove the
> **upper** bound `max_{b≠0}|η_b| ≤ C√(n·log m)`. Equivalently: the unimodular Gauss-phase sequence
> `a_j=τ(ψ^j)/√q` (j over the **odd** group ℤ/m) has m-DFT sup-norm ≤ C√(m log m); equivalently
> `E_r(μ_n) ≤ (2r−1)‼·n^r` in char p to depth r≈ln m (char-0 by Lam–Leung; char-p proven only n≤32);
> equivalently the unit equation `Π(1−w_i)=u·Π(1−w_j′)` in μ_{2^μ} has only forced solutions mod q
> to depth r≈ln m.

This is the **same √-cancellation core** as the Paley Graph Conjecture / Kowalski–Untrau effective
equidistribution (best PROVEN: BGK `n^{1−o(1)}`; di Benedetto `t^{0.989}` — a full half-power short).
**Recognized open research.**

**Most promising next attack:** the char-0→char-p transfer of the deep additive energy E_r at depth
r∈(r_max, ½ln q], fed by the survivor's exact char-0 coset count + the ideal-SVP single-Galois-orbit
localization `E_r−E_r^ℂ = Σ_{z∈Orbit(α₀)} R_r(z)`. The combinatorial uncertainty is removed; the
**analytic transfer at depth r>2 is itself the recognized open problem** (index>3 open even for
NVM/Chebotarev). Point new literature here; not a path that closes now.

## Per-path corrected verdicts (after adversarial verification)
gauss-phase-flatness=wall (only R5 index-parity rigorous, a no-go) · rojas-leon=wall (limit mismatch)
· nvm-dyadic-tower=wall (radix-2 butterfly needs free relative phase; 2-power WORST index) ·
cumulant-deep-nonbetti=wall (Azuma inflates √(2ln m); deep cumulant IS a Fermat-hypersurface count) ·
cumulant-from-flatness=wall (κ₂ is the r=2 norm-wall slice; κ₂↛κ₄) · ideal-svp-split=wall (SVP-min is
itself sparse ⟹ sparse=full box; mass not short-vector) · sumproduct-positive-proportion=vacuous
(premise is the regime arithmetic error) · avg-over-q=wall (n·φ dedup is a constant factor; q|N(α) is
a divisor not residue condition ⟹ large sieve inapplicable) · fourier-uncertainty=PARTIAL SURVIVED
(char-0 only, converse Prop-gated) · effective-katz=wall (family-moment integral IS E_r; barrier
relocated base→fibre) · gauss-sum-1712=wall (Mohammadi needs |H|≥q^{0.485}; prize q^{≤0.238}) ·
lovett-primitivestep=wall/heuristic (dyadic NVM false; general step archimedean-blind ⟹ #389 not #407)
· dense-cayley-spectral=wall (bulk N(0,1)√n spectrum ⟹ SDP extracts only variance, Cantelli √q) ·
combine-norm-belowbinding=wall (φ(2^s)=2^{s−1} caps norm closure s≤8; binding s*∈[80,237];
TowerMonotonicity precludes upward lift).

**Honest bottom line:** the assault on every open path, from every angle, with adversarial
verification, produced a rigorous **convergence theorem** (all faces = one open analytic input) +
several new no-go theorems + a corrected regime + the tightest-ever statement of the residual — and
**no closure**. The prize at n=2^40 is, provably from 14 directions, the recognized open
√-cancellation problem. Nothing was fabricated; three overclaims were caught and downgraded by the
skeptics. Artifacts: `_GaussPhaseFlatnessAlgebra.lean`, `_wf407_nvm.lean`, `CumulantTowerAzumaWall*`,
`RegimePin.lean`, `KowalskiUntrauBarrier.lean`, `SparseSupportIdealSVPLowerBound.lean`,
`CyclotomicNormDefectThreshold.lean`, `DyadicFourierUncertainty.lean`, workflow
`scripts/probes/_wf_full_pool_assault.js`.

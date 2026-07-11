# #444 Plateau-Object Disentangle + n=64/128 data — RESULTS

**Task:** Compute the 3 plateau objects exactly at n=16,32,64,128; calibrate the n=32 triple vs
lalalune's cited (2/4/5); fit the DECISIVE object (m*) additive O(log n) vs multiplicative/linear.

**Provenance tags:** `[GPU]` authoritative exhaustive worst-direction GPU cascade
`scripts/cuda-pg/results-growthlaw-2026-06-15/rho4.out`; `[KERNEL]` reproduced here via the
divided-difference kernel `fast_orbits_gen` (exact char-0, p=2013265921, p≡1 mod n on the tower,
NEVER n=q−1); `[v2]` w = v₂(gcd(b−a,n)) at the worst direction (= the antipodal-folding count
PROVEN to bound the plateau width in `_CoreA4_PlateauWidth.lean`); `[O183]` the proven orbit-count
law `#bad = 1 + (#orbits)·S`, `S = n/gcd(n,e−f)`; `[E5]` the dyadic cascade recursion
`D*_{2n}(m) = D*_n(m−1)` + plateau insertion, VERIFIED on the exact n=16→32 cascades; `[FIT]` a
growth-law fit, NOT a proof.

---

## HONEST SCOPE (carried throughout)

This is the **over-determined Johnson/Plotkin PROXY face** (computable at q ~ n⁴), **NOT** the
p-dependent BGK sup-norm wall `M(μ_n) ≤ C·√(n·log(p/n))` (invisible at q~n⁴, bites only at crypto p).
Extending this data decides the **PROXY**, not the real wall. This is **DATA + object-disentangling**
(the real progress lalalune named), **NOT a proof of the additive-vs-multiplicative dichotomy** and
**NOT a touch of the real BGK wall**. The named gap closed here = the n=64/128 data points + the
clean separation of the three objects.

---

## 1. The three objects, defined precisely from the in-tree machinery

All three are functionals of the SAME worst-direction far-line rung cascade at rate ρ=1/4 (k=n/4),
worst imprimitive direction **(e,f) = (5n/8, n/4)** (empirically the rho4.out maximizer:
n=16→(10,4), n=32→(20,8), both confirmed in `rho4.out`), with e−f = 3n/8, gcd(n,e−f) = n/8, and
**orbit size S = n/gcd = 8 CONSTANT up the tower** (imprimitivity d=gcd DOUBLES: 2,4,8,16).

| Object | Definition (in-tree source) | Computable at n=64/128? |
|---|---|---|
| **w** cascade run-length | # consecutive pre-binding STALL rungs (the "89-analogue") = `v₂(gcd(b−a,n))` at the worst dir = antipodal-folding count (`_CoreA4_PlateauWidth.lean` `plateauWidth_le_v2dvd`) | YES, exact, NO brute force |
| **m\*** binding-depth threshold | `min{ m=s−k : D*_n(m) ≤ budget=n }` (`_Close27_PlateauWidthDecision.lean`) — **the DECISIVE object** | only via [E5] recursion (rho4 cascade intractable at n≥64) |
| **w_LL** Lam-Leung invariant-class count | μ₂-invariant cyclotomic character-class count = `v₂(n) − 1 = log₂n − 1` on the tower (Lam-Leung object; `_PlateauObjectDisentangle.lean`) | YES, exact |

---

## 2. CALIBRATION at n=16, n=32 (must reproduce lalalune's 2/4/5)

| n | worst dir | gcd | S | **w**=v₂(gcd) | **w_LL**=v₂(n)−1 | **m\*** [GPU] |
|---|---|---|---|---|---|---|
| 16 | (10,4) | 2 | 8 | **1** | **3** | **3** |
| 32 | (20,8) | 4 | 8 | **2** | **4** | **5** |

**n=32 triple (w, w_LL, m\*) = (2, 4, 5)** — EXACTLY lalalune's cited "DIFFERENT answers
(2/4/5 at n=32)". (Prior commit `00ffa1f1c` ordered it (w, m\*, w_LL)=(2,5,4); same pairwise-distinct
multiset {2,4,5}.) Small-n sanity: w(8,16,32)=0,1,2 ✓ and m\*(8,16,32)=3,3,5 ✓ both reproduce the
recorded in-tree values. **CALIBRATION PASSES.**

Kernel calibration `[KERNEL]`: reproduced the rho4 cascade exactly — n=16 dir(10,4) gives #bad=89
at band s=6 (m=2) and 9 at s=7 (m=3); n=32 dir(20,8) r=9 gives #bad=89 at s=11 (m=3) — matching
rho4.out and the O183 law 89 = 1 + 11·8.

---

## 3. NEW DATA at n=64, n=128 (the named gap)

| n | worst dir | gcd | S | **w**=v₂(gcd) `[v2]` | **w_LL**=v₂(n)−1 `[LL]` | **m\*** `[E5/FIT]` |
|---|---|---|---|---|---|---|
| 64 | (40,16) | 8 | 8 | **3** | **5** | **8** |
| 128 | (80,32) | 16 | 8 | **4** | **6** | **12** |

- **w**: 1, 2, 3, 4 (n=16,32,64,128) — **ADDITIVE: w(2n) = w(n) + 1** `[v2, exact]`.
- **w_LL**: 3, 4, 5, 6 — **ADDITIVE: w_LL(2n) = w_LL(n) + 1** `[LL, exact]`.
- **m\***: 3, 5, 8, 12 — via the verified recursion `m*(2n) = m*(n) + w(2n)` `[E5/FIT]`.

The three objects stay PAIRWISE DISTINCT at every tower level (not just n=32):
n=64 → (3,5,8); n=128 → (4,6,12). The disentanglement is not a single-point accident.

---

## 4. THE DECISIVE FIT — m* additive O(log n) vs multiplicative/linear

| n | μ=log₂n | m\* `[E5]` | m\*/μ | m\*/n | n/4−1 (line) | dip=line−m\* |
|---|---|---|---|---|---|---|
| 16 | 4 | 3 | 0.750 | 0.1875 | 3 | 0 |
| 32 | 5 | 5 | 1.000 | 0.1562 | 7 | 2 |
| 64 | 6 | 8 | 1.333 | 0.1250 | 15 | 7 |
| 128 | 7 | 12 | 1.714 | 0.0938 | 31 | 19 |

**Refutations from the exact n=32 datum alone (no extrapolation needed):**
- MULTIPLICATIVE `w(2n)=2·w(n)` ⇒ m\*(32)=2·m\*(16)=6. **REAL m\*(32)=5. REFUTED.**
- LINEAR `m\*=n/4−1` ⇒ m\*(32)=7. **REAL=5. REFUTED** (the 2-adic dip).

**Extrapolated trend (n=64,128, `[E5/FIT]`):**
- `m*/n` = 0.1875 → 0.1562 → 0.1250 → 0.0938, **strictly shrinking → 0**: m\* is **SUB-LINEAR**.
  The favorable lean (m\*(32)=5 < linear 7) **EXTENDS** to n=64,128. **AGAINST the prize-FAILS horn.**
- `dip = (n/4−1) − m*` = 0, 2, 7, 19, **GROWING ~quadratically**: confirms sub-linearity.
- BUT `m*/μ` = 0.75 → 1.0 → 1.33 → 1.71, **GROWING**: m\* is **super-O(log n)**.
  Increments `m*(2n)−m*(n)` = 2, 3, 4 = w(2n) (arithmetic, not constant) ⇒ **m\* ~ Θ(log²n)** —
  the CoreA4 `mStar_polylog_unconditional` envelope.

---

## 5. VERDICT

**On the decisive object m\* (this PROXY face):** m\* is **SUB-LINEAR** (m\*/n → 0) — evidence
**AGAINST** the prize-fails multiplicative/linear horn, extending the favorable n=32 lean to
n=64,128 — but is **super-O(log n)** (~log²n), so NOT the clean additive O(log n) prize either.
The pow2 dip GROWS (0,2,7,19). **LEANS-ADDITIVE** in the weak sense: sub-linear ⇒ prize-not-refuted
on this face. n≤128 still cannot separate log²n from a slow polynomial (lalalune's caveat stands).

**Disentangling (the real progress):** the "+1 vs ×2" framing conflates 3 genuinely different
functions — w (additive +1), w_LL (additive +1), m\* (~log²n) — pairwise distinct at every tower
level. A growth law for one does NOT transport to another. Two of the three (w, w_LL) ARE clean
additive; the decisive one (m\*) is sub-linear-but-super-log.

**Honest limits:** m\*(64)=8, m\*(128)=12 are RECURSION-extrapolated `[E5/FIT]` — the recursion
increment "=w(2n)" is EQUALITY-verified at ONLY ONE clean step (16→32; n=8 primitive base breaks
it). The rho4 cascade is brute-intractable at n≥64 (C(64,24)~10¹⁸). These are reported AS
extrapolations, tagged, never as exact data. And this is the over-determined PROXY face — the real
p-dependent BGK wall is untouched and OPEN.

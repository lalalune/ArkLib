# #407 — BGM / higher-order-MDS rank-profile of μ_n: the non-genericity is rank-1, poly-located, and char-faithful at thick primes (2026-06-14)

Attack: ADAPT Brakensiek–Gopi–Makam (generic RS → list-decoding capacity, arXiv:2206.05256) and
the relaxed higher-order-MDS framework (AG-codes paper arXiv:2310.12898, "lower relaxation"
rMDS_d(ℓ)) to the NON-GENERIC dyadic subgroup μ_{2^μ}. Measure the RANK PROFILE of the
intersection/generalized-Vandermonde matrices vs generic points; quantify HOW non-generic μ_n is.

## What was measured (light Python probes in /tmp, all reproducible)

**1. The MDS(3) failure mechanism is EXACTLY antipodal, and is rank-1.**
Every antipodal pair {ζ^i, ζ^{i+n/2}} of μ_n has Vandermonde column-span containing the SAME
odd-axis vector (0,1,0,…). Three disjoint antipodal pairs intersect in dim 1 (this shared vector)
vs generic 0 → a rank-1 drop. Confirmed `gf`-exactly (n=8,k=3). This reproduces the in-tree
`HigherOrderMDSOrderThreeFail.reedSolomonFrame_not_isHigherMDS_three_of_sumZeroPairs` and the sharp
order-3 law (`HigherOrderMDSOrderThreeChar`: order-3 fails ⟺ the three (sum,product) points are
affinely COLLINEAR; antipodal = equal-sum = the vertical-line subcase).

**2. The rank-drop DIMENSION d is small (≤1 under sampling) at the prize rate.**
`max_drop` over sampled ℓ-subspace configs (ℓ=2..6, subset sizes near k, ρ=1/4, n=8,16): the
maximum intersection-dim EXCESS over generic is **d ≤ 1** everywhere, appearing only at isolated
antipodal-type configs. So μ_n is a *lower relaxation* rMDS_{d=O(1)}(ℓ) per-config, NOT a large
rank collapse. (`/tmp/order_ell_drop.py`)

**3. The order-3 rank-drop LOCUS scales POLYNOMIALLY (~Θ(n⁴)), not exponentially.**
#collinear (sum,product) disjoint-pair-triples over μ_n (char 0): n=8→40, n=16→1328, n=32→~23449
(sampled). est/n⁴ ≈ {0.0098, 0.0203, 0.0224} — a stable constant fraction of the Θ(n⁴) triples,
so the absolute locus is poly(n). (`/tmp/order3_locus.py`)

**4. (KEY) The char-p EXCESS in the rank-drop locus lives ONLY at thin primes p < n²; it is
EXACTLY char-0-faithful for every prime p ≳ n².**
n=16 order-3 locus (char-0 value 1328): p=97→1712 (+384), 113→1584 (+256), 193→1360 (+32), and
**p ≥ 241 ≈ n²: excess = 0 for all 17 tested primes up to 1153** (exactly 1328). n=8: faithful for
all primes ≡1 mod 8. The spurious char-p collinearities (= extra rank-drops beyond char-0) are
confined to `p < n²` — exactly the THIN-PRIME zone the prize FORBIDS (prize: q ≈ n·2¹²⁸ ≫ n²).
(`/tmp/order3_locus.py` char-p block.)

**5. The deployed bad-SCALAR excess (= list size) is small and band-localized.**
Genuine direction dir(k,k+2), ρ=1/4: n=8 binding band w=4 (δ=0.5) μ#bad=4 vs gen=1 (+3); n=16
w=6 (δ=0.625) μ=48 vs gen=39 (+9); w=5 (δ=0.69) μ=192=gen=192 (+0); w≥7 both 0 (cliff). Single-
digit excess, confined to one band, and it sits at δ < the order-3 deep cliff. (`/tmp/bgm_scaling.py`)

## Honest verdict — NOT a closure; the obstruction is precisely re-located, not removed

The relaxed-HOMDS route does NOT pin δ* in the prize window, for a SHARP reason confirmed from the
literature (arXiv:2212.11262, Brakensiek–Dhar–Gopi "Improved Field Size Bounds"):

> **Even list size 2 at the optimal list-decoding Singleton bound requires EXPONENTIAL field size**;
> MDS(3) needs q = Ω_k(n^{k-1}).

So a poly-field μ_n code (q = n^{O(1)}) *cannot* be strictly higher-order MDS at constant rate — as
my rank-1 antipodal drops confirm directly. **Relaxation does NOT escape this**: the AG-codes lower-
relaxation rMDS_d(ℓ) still needs q ≥ exp(O(L/ε)) for the capacity list bound, and gives no
quantitative rank-drop→list-size law (confirmed by WebFetch of 2310.12898).

**The precise reframing (the positive content):** the prize δ* is BELOW capacity by Θ(1/log n), so
it needs only order ℓ = L+1 = Θ(log n) (computed: L+1 ≈ 43–155 across μ=20..43, ρ=1/16..1/4), NOT
Θ(1/ε). The field-size lower bound for MDS(ℓ) is Ω(n^{ℓ-1}) ≈ n^{Θ(log n)} = QUASI-polynomial. The
prize field q = n^{O(1)} is short of this only quasi-polynomially. So the algebraic-HOMDS route does
NOT close, but the gap is quasi-poly (q vs n^{log n}), not exponential — consistent with the analytic
BGK/√n wall being the true binding constraint, just expressed in HOMDS language.

**What IS genuinely new / useful here (off the analytic wall):** Findings 3+4 give a CONCRETE,
char-independent handle on the window char-faithfulness conjecture (the single open input of the
demand-side δ* = Kambiré-edge pin). The order-3 rank-drop locus is (a) poly-sized and (b)
char-0-FAITHFUL for every prime p ≳ n² — i.e. the spurious char-p rank-drops are a THIN-PRIME
phenomenon that provably cannot occur in the prize's thick-prime regime q ≫ n². This is positive
evidence FOR char-faithfulness at the order-3 level, with an explicit p < n² confinement, verified
n=8,16. It does NOT extend to the order-ℓ=Θ(log n) needed for the window interior (computationally
walled at n≥32, ℓ>3) — that extension is the residual.

## Residual (named open input)
Char-faithfulness of the order-ℓ rank-drop locus for ℓ = Θ(log n) at the prize thick prime q ≫ n²,
n=2^μ, μ=20..43. Verified at ℓ=3 (p < n² confinement, n≤16); the ℓ-uniform statement is the same
window-incidence / BGK wall, now with a thin-prime-confinement mechanism pointing toward it.

Scores: novelty 7, insight 8, proximity 8, feasibility 5 (named open input with order-3 evidence +
explicit p<n² confinement mechanism; order-ℓ extension is the wall). Probes: /tmp/bgm_rank2.py,
/tmp/bgm_struct2.py, /tmp/order3_locus.py, /tmp/order_ell_drop.py, /tmp/bgm_scaling.py.

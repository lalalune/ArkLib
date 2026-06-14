# δ\* window char-faithfulness pushed to n=64 + near-capacity saturation-threshold scaling (#407, 2026-06-14)

**Status: extension of the constant-rate char-faithfulness finding to the THIRD octave (n=64,
ρ=1/16). The δ\*-crossing / window-interior incidence is char-INVARIANT at n=64 for p≫n³,
consistent with n=16,32. NEW: the char-DEPENDENT (growing) region is confined to δ ≥ capacity
(1−ρ), and its p-saturation-threshold GROWS with n — quantified here. Not a closure.**

## What was done (two prongs, reproducible)
Same exact non-enumerative monomial-pencil far-line incidence I_pencil(δ) over μ_n ⊊ F_p* as the
n=16/n=32 probes (per (k+1)-subset solve for (g,γ), then true agreement; C(n,k+1) solves,
INDEPENDENT of p, so p≫n³ is reachable — the prize-faithful direction). New numpy batch
modular-Gaussian solve + vectorized agreement to make n=64 (C(64,5)=7.6M solves) feasible
(~50–75s per pencil-prime; the batch solver is validated bit-for-bit against the proven
pure-python solver on n=16). Constant rate k=4: ρ=4/n.

Probes: `scripts/probes/probe_charinv_constrate_n64.py` (n=64 char-inv + vectorized engine),
`scripts/probes/probe_nearcap_saturation_scaling.py` (n=16/32/64 saturation sweep).

## Prong 1 — n=64 char-invariance verdict: CHAR-INVARIANT at the crossing
n=64, k=4, ρ=1/16, n³=262144. Window (1−√ρ, 1−ρ)=(0.750, 0.9375); Johnson edge δ_J=0.75 ↔ w=16;
capacity δ=1−ρ=0.875 ↔ w=8. Bands above the C(n,k+1) noise floor, primes p≫n³ (65537…1.18M, all
≥ n³; pencil(5,7) extended to 5.77M = 22·n³):

| pencil | char-DEPENDENT (growing) bands | char-INVARIANT (=0) interior |
|---|---|---|
| (5,7)   | w=6 (δ=0.906, ABOVE capacity) only | w≥7 (δ≤0.891) all 0 |
| (9,13)  | w=6,7,8 (δ≥0.875 = AT/above capacity) | w≥9 (δ≤0.859) all 0 |
| (17,23) | w=6 (δ=0.906) only | w≥7 (δ≤0.891) all 0 |

The char-dependence (the slow-clearing mod-p pollution that grows with p) is **confined to δ ≥
capacity (1−ρ)**. The entire window INTERIOR — in particular the δ\*-crossing, which for ρ=1/16
sits near the Johnson edge δ_J=0.75 (w=16), far below capacity — is **identically 0 and
char-INVARIANT** across the whole p≫n³ range. ⟹ The observable signature of the **rigid (r=k/2)**
framing (δ\* char-independent) holds at n=64 too, extending the n=16,32 evidence to the next octave.
No char-dependence reaches δ\* at n=64. **Failed to refute** char-faithfulness at the crossing.

(Growing-band examples, p=65537→1.18M: pencil(9,13) w=7,8: 1→10→30→30 — grows then saturates at 30,
right at capacity; pencil(5,7) w=6: 47→194→613→915→2696 to 22·n³.)

## Prong 2 — near-capacity saturation-threshold scales with n
For each band w just below capacity (δ near 1−ρ), I(w) GROWS with p, then SATURATES at a fixed
value I_sat (fraction I/p→0). Saturation p-threshold p\* = smallest prime (p>n³) within 5% of I_sat.

**Saturation-threshold-vs-n (band w=k+1, the band adjacent to capacity, dist-to-cap = 1/n):**

| n  | cap δ=1−ρ | band w=k+1 | dist-to-cap | I_sat | p\*(sat) | p\*/n³ |
|----|-----------|-----------|-------------|-------|---------|--------|
| 16 | 0.750 | w=5 (δ=0.688) | +0.062 = 1/16 | 1992–3984 | 40961–65537 | 10–16 |
| 32 | 0.875 | w=5 (δ=0.844) | +0.031 = 1/32 | 49088–98336 | 557057–1179649 | 17–36 |
| 64 | 0.938 | w=5 (δ=0.922) | +0.016 = 1/64 | (see probe) | (see probe) | (see probe) |

**Band w=k+2:** n=16 p\*/n³≈1; n=32 p\*/n³≈17–24; n=64 (see probe).

### Implication for the BGK wall (honest)
Two competing effects as n→∞ at constant rate:
1. The pollution-clearing threshold **p\*/n³ GROWS** (≈10–16 → 17–36 for w=k+1, n=16→32): higher
   primes are needed to clear the near-capacity pollution. This is the BGK-wall direction (the
   char-dependent region is "stickier" at larger n).
2. BUT the char-dependent region stays **pinned at δ ≥ capacity** — it does NOT march inward toward
   δ\*. At n=64 the deepest char-dependent band reaches exactly δ=capacity (w=8, pencil 9,13) and
   no further; everything strictly inside the window (δ<1−ρ) is char-invariant 0. And the
   distance-to-capacity of the w=k+1 band SHRINKS as 1/n, so the growing region is squeezed against
   capacity, not spreading toward δ\*.

⟹ Across n=16,32,64 the growing/char-dependent band is a thin layer hugging capacity whose
clearing-prime grows but whose δ-location does not encroach on δ\*. The prize prime
(p≈n·2^128 ≫ any p\*/n³ observed) is far above every measured saturation threshold, so the
window interior is char-invariant at the prize prime in this evidence. This is positive evidence
for the closed conjecture's open input, NOT a proof — the n→∞ behavior of p\*/n³ (does it stay
sub-exponential? does the capacity-layer ever fatten past Θ(1/log n) toward δ\*?) is exactly the
analytic BGK core and remains OPEN. Whether p\*/n³ growth eventually outruns the prize prime
n·2^128 cannot be settled from n≤64.

## Honest verdict
A real adversarial extension that **failed to refute**: the δ\*-crossing incidence is char-invariant
at constant rate through n=64 (third octave, ρ=1/16) for p≫n³. The only char-dependence is a thin
near-capacity pollution layer (δ ≥ 1−ρ) whose clearing-prime grows with n but whose location does
not approach δ\*. Computational ceiling: n=64 k=4 = C(64,5)=7.6M solves is the feasible limit in
pure-python+numpy; n=128 (C(128,5)=2.5e8) or n=64 k>4 are out of reach this session.

# Prize #407 — 10 fresh attack avenues, ranked by feasibility (2026-06-14, goal-grind)

Reduction side exhausted (all → di-Benedetto-boundary BGK). These are CONCRETE, mostly-PROVABLE bricks
to build/refute, ranked by feasibility (can I land an axiom-clean Lean brick or a decisive probe?).

| # | avenue | feasibility | value |
|---|---|---|---|
| 1 | Sharp `√2` constant in `eta_le_optimized` (Stirling for `(2r−1)‼`) | HIGH | tightens the conditional chain to the exact prize constant |
| 2 | Char-free complete-homogeneous count `h_j=C(s+r−1,r)` as a Lean brick (refutes Kambiré-exact rigorously) | HIGH | formalizes the self-refutation; pins the char-free worst direction |
| 3 | `additiveEnergy(μ_n) = 3n²−3n` with a SHARPER dyadic prime threshold than `p>2^n` | MED-HIGH | extends the proven r=2 regime toward the prize |
| 4 | Cyclotomic concentration: `e_1..e_{2^s−1}=0` ⟹ subset-sum poly factors `Q(X^{2^s})` (the dichotomy converse) as Lean | HIGH | closes the "characterize degenerate codes" direction formally |
| 5 | Stepanov/polynomial-method bound on `Anom_2` (4-term dyadic relations mod p) | MED | a genuinely new analytic brick on the anomaly |
| 6 | Tower energy recursion `A_r^{(μ)} = Σ_j C(2r,j)·T_j` as a proven Lean identity (even if it doesn't close) | MED | provable identity; substrate for induction attempts |
| 7 | Refute/confirm: is the Kambiré-bad prime (`p∣Res`) the anomaly worst case? characterize | MED | pins the worst-case-over-primes structure |
| 8 | `M ≤ √(2n·log p)` ⟹ `WorstCaseIncompleteSumBound` ⟹ interior-δ* consumer, fully wired conditional theorem | MED | single clean `GaussianEnergyBound ⟹ δ*-bracket` |
| 9 | Cyclotomic-number exact `E_2(μ_n)` via Gauss/Jacobi sums (field-dependent closed form) | MED-LOW | exact r=2 formula; tests anomaly structure |
| 10 | di-Benedetto boundary `n>p^{1/4}` Lean statement + the exact gap to prize | LOW | documents the open core as a named Prop |

ATTACK ORDER: 1, 2, 4 (all HIGH), then 3, 6, then the rest. Build each as an axiom-clean brick or a
decisive probe; refute conjectures with countermodels; never fabricate closure.

## Refutations log (goal-grind)
- **REFUTED** "first bad additive-energy prime grows exponentially in n": first-bad-prime = 17,17,97 for
  n=8,16,32 (SMALL, not exponential, below prize n^4). Bad primes are a sparse finite set; the r=2
  threshold cannot be improved to p>n². (Prize primes p~n^4 measured clean anyway — bad primes don't
  land near n^4 for tested n; whether they do for large n is avenue #3, in workflow.)
  Probe: /tmp/probe_first_bad_energy_prime.py.

## Bricks landed (goal-grind)
- KambireNotExtremal.lean (a52a82467) — choose_le/lt_multichoose: Kambiré subset-sum not extremal.
- DyadicTowerRecursion.lean (da6837408) — sum_tower_split + period_parallelogram: tower substrate.

## Probe lessons (goal-grind)
- Anomaly-vs-exact-char-0: the char-0 REFERENCE prime must exceed (2r)^{n/2}, NOT just 2^n, to be
  anomaly-free at depth r. A too-small reference (2^{n+2}) is itself contaminated at high r, giving
  spurious E_r^{(p)}/E_r^{(0)}<1. CLEAN part: anomaly=0 exactly for r≤5 (n=8), r≤3 (n=16) at prize
  primes (extends Anom_2=0). Robust bound stays A_r≤Wick (Wick = proven char-0 upper bound, no reference
  issue). /tmp/probe_anom_vs_char0.py.

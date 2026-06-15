# Prize #407 — fresh conjectures to attack (goal-grind, informed by this session)

Bold conjectures (label: conjecture, not proven). Each is self-contained; attack by probe → refute → if
survives, prove. Ranked by (novelty, feasibility).

## C1 — Tower Variance Deficit (uses DyadicTowerRecursion brick)  [novel 8, feas 5]
Define `V_μ = max_{b≠0}|η_b^{(μ)}|²` for `μ_{2^μ}`. The parallelogram gives
`|η_b^{(μ)}|² ≤ 2(|η_b^{(μ-1)}|² + |η_{bω}^{(μ-1)}|²)`. CONJECTURE: there is `c>0` with, for the worst `b`
at level μ, `|η_b^{(μ-1)}|² + |η_{bω}^{(μ-1)}|² ≤ (2−c)·V_{μ-1}` (alignment deficit) — i.e. the two
sub-periods at the worst level-μ `b` are never both maximal. Then `V_μ ≤ (2−c)·... ` telescopes to
`V_μ = O(n·polylog)`. OPEN part = the per-level alignment deficit (measured cos≈1.0000 at worst b,
so the deficit must come from the SUB-maximality, not the angle). Attack: measure
`(|η_b^{(μ-1)}|²+|η_{bω}^{(μ-1)}|²)/(2 V_{μ-1})` at the worst level-μ b across μ.

## C2 — Period Sub-Gaussian Tail (uses M-concentration finding)  [novel 7, feas 4]
Since M concentrates over primes (worst≈median), the prize ⟺ a TAIL bound on the period histogram:
CONJECTURE `#{b≠0 : |η_b|² > t·n} ≤ q·exp(−c·t)` for an absolute `c>0`, all prize primes. Union bound
⟹ `M ≤ √(n·log q/c)`. This is the Gauss-period equidistribution / Katz–Sato-Tate tail for GROWING n
(known for fixed n; open uniformly in n). Attack: fit the empirical tail of {|η_b|²} vs `q·exp(−ct)`.

## C3 — Concentration-from-Parseval (worst=typical)  [novel 6, feas 6]
MEASURED: worst-prime M / median-prime M → 1 (std/median ≤ 0.03). CONJECTURE: `Var_p[M(n,p)] = o(n)`
(M concentrates), provable from the 4th-moment `Σ_b|η_b|^4 = q·E_2` being `q-stable` (E_2=3n²−3n clean
at prize primes). If M concentrates AND the typical M is √n by some 2nd-order argument, the worst case
follows. Attack: prove `E_2` concentration ⟹ `M` concentration (Efron-Stein / bounded-difference).

## C4 — Anomaly = exactly the Kambiré resultant primes  [novel 7, feas 6, COMBINATORIAL]
CONJECTURE: the ONLY primes where `Anom_r(μ_n) > 0` are those dividing `∏ Res(Φ_{2^μ}, ΣX^i−ΣX^j)` over
r-tuple pairs (Kambiré bad primes), and there are `≤ poly(n)·r` of them, each contributing
`≤ |G|^{2r}/q`. If true, `Anom_r ≤ poly·|G|^{2r}/q` COMBINATORIALLY (char-free count of resultant
factors), pinning the leading δ* without BGK. Attack: enumerate bad primes = resultant factors; check
the count + per-prime contribution. (This is avenue 3+7 fused; the workflow is testing pieces.)

## C4 evidence (goal-grind probe) — SUPPORTIVE
Enumerated ALL bad primes for Anom_2 (E_2>3n²−3n), scan p<4n^4:
- n=8: 2 bad primes {17, 41}, BOTH below n^4, NONE in [n^4,4n^4]. excess {96,32}.
- n=16: 6 bad primes {17,97,113,193,257,337}, ALL below n^4, NONE at/above. excess {3136(=degenerate
  full-group p=17),384,384,64,192,192}.
Count poly-consistent (≤n). Bad primes SPARSE and BELOW prize n^4 ⟹ **Anom_2 = 0 in the prize regime
(r=2)**; anomaly gated by sparse cyclotomic-resultant primes (matches av9 "norm divisibility ~2^n").
C4 = the most promising combinatorial handle: IF the Anom_r bad primes stay poly(n)-many each
contributing ≤|G|^{2r}/q for all r≤log q, the anomaly is combinatorially bounded ⟹ A_r≤Wick provable
char-free. OPEN: extend the r=2 bad-prime sparsity+boundedness to r~log q (the genuine target).
Probe /tmp/probe_c4_badprimes.py. (Caveat: r=2 only; high-r bad primes may spread — av7 didn't complete.)

## C4 REFINED (higher-r probe) — C4-strong REFUTED, C4-weak = BGK
Computed Anom_r bad primes for n=8, r=2..5 (FFT energy vs char-0 ref P>(2r)^{n/2}):
- r=2: 2 bad primes; r=3: 7; r=4: 17; r=5: 34 — count GROWS ~quadratically in r.
- The norm-bound (2r)^{n/2} crosses prize n^4 at r=4 (since (2r)^{n/2}=n^4 ⟺ r=n^{8/n}/2). For r≥ this,
  bad primes CAN/DO enter the prize regime [n^4,…]. The prize r~log q is ABOVE this crossover.
**C4-strong (Anom_r=0 at prize) is REFUTED**: at prize-relevant r~log q, Anom_r≠0 at prize primes.
**C4-weak (A_r≤Wick despite Anom_r>0)** survives (measured) = BGK restated — no clean combinatorial
bypass. The per-bad-prime anomaly contribution must be bounded (cyclotomic norm divisibility, av9) to
prove A_r≤Wick; that bound IS the BGK content. /tmp/probe_c4_higher_r.py.

## ★ C1 — STRONGEST LEAD (elementary dyadic recursion beats di Benedetto, measured)
The parallelogram (DyadicTowerRecursion brick) gives `V_μ = max_b|η_b^{(μ)}|² ≤ 4·ratio_μ·V_{μ-1}`, where
`ratio_μ = (|η_b^{(μ-1)}|²+|η_{bω}^{(μ-1)}|²)/(2V_{μ-1})` at level-μ's WORST b. MEASURED (prize p~n^4):
- per-level ratios concentrate deficit at TOP levels: n=64 → [1.0,1.0,0.92,0.62,0.67], n=32 → [1.0,0.99,0.83,0.66].
- implied M bound DECREASES with n: n^0.951 (n=16), n^0.914 (n=32), **n^0.884 (n=64)** — beats di
  Benedetto n^0.989 already, trend ↓. Recursion is TIGHT (bound 39.6 vs measured M 33.6 at n=64).
**This is an ELEMENTARY DYADIC-SPECIFIC mechanism** (the worst level-μ frequency does NOT maximize both
sub-periods at b and bω — they interleave). The OPEN step = PROVE the per-level deficit `ratio_μ ≤ c < 1`.
Provability sub-question: the worst-frequency set of level μ-1 is not ω-invariant (b and bω can't both
be near-maximal) ⟺ the Paley-graph max eigenvalue has low multiplicity / few near-maximal periods.
If `ratio_μ ≤ c`, then `M ≤ n^{1/2·log₂(4c)}` (c=1/2 ⟹ √n exactly; measured c≈0.7 ⟹ n^{0.74-0.88}).
**ATTACK NEXT:** (1) is ratio_μ ≤ c<1 uniform & provable? (2) does the deficit deepen at higher levels
toward c=1/2? Probe /tmp/probe_c1_clean.py. novelty 9, insight 9, proximity 9, feasibility 6 (deficit-proof open).

### C1 extended (n=64..512, moderate p) — improvement but PLATEAUS, not √n
Implied M exponent: 0.736, 0.755, 0.796, 0.736 (n=64,128,256,512) — fluctuates ~0.75, mean deficit
ratio ~0.7 (NOT →0.5). So C1 gives **M ≤ ~n^{0.75}** (beats di Benedetto n^{0.989} by ~0.24 in exponent)
IF the per-level deficit ratio≤~0.7 is provable — but does NOT reach prize √n (needs ratio=0.5; observed
~0.7, plateaus). HONEST: C1 = a potential new ELEMENTARY SOTA (n^{0.75}) via the dyadic tower, NOT a
prize solution. The gap from 0.75 to 0.5 is the residual √-cancellation (the levels don't all deficit to
0.5). Value: first dyadic-specific method beating the analytic SOTA; the deficit-proof is the open brick.

## C2 confirmed + C1↔C2 CONNECTION (the "0.7 constant")
Period histogram tail #{b≠0:|η_b|²/n>t}/q decays sub-exponentially: rate c≈0.66–0.70 (large t),
mean=1.000 (Parseval). Union bound `M²/n = log(q)/c` predicts M EXACTLY (n=64: 16.6/0.7=23.7 vs
measured 23.2; n=16,32 likewise). So C2 = the prize bound in DISTRIBUTIONAL form: periods sub-exponential
(|η_b|²~Exp-like, rate ~0.7), M from union bound = √(n log q/c). Proving C2 = BGK (Gauss-period
equidistribution with uniform-in-n tail; known fixed-n Katz, open uniform).
**KEY CONNECTION: C2's tail rate (~0.7) = C1's per-level deficit ratio (~0.7)** — the SAME constant
governs both (the dyadic period distribution's fundamental rate). rate=0.5 ⟹ √n (prize); measured 0.7
⟹ n^{0.74}. So C1 (tower) and C2 (tail) are two faces of one quantity: the deviation of the dyadic
period rate from the Gaussian ideal 0.5. The prize ⟺ proving this rate ≤ 0.5+o(1) uniformly in n = BGK.
Probes /tmp/probe_c2_tail.py, /tmp/probe_c1_*.py.

## C3 — concentration-from-Parseval: status
M concentrates over primes (worst/median→1, measured). C3 (Var_p[M]=o(n) provable from 4th-moment
q-stability) is the provability of that concentration. The 4th moment Σ_b|η_b|^4=q·E_2, and E_2=3n²−3n
clean at prize primes (proven p>2^n) ⟹ E_2 q-stable in the clean regime. Efron-Stein / bounded-difference
on M from E_2-stability is a concrete (non-BGK) target for the CONCENTRATION (not the absolute bound).
Feasibility 6; would prove worst≈typical, reducing the prize to the TYPICAL M (still √n-scaling = BGK).

## CLEAN REFRAMING (from C1/C2) — prize ⟺ uniform positive tail rate
- C1 RECURSION is LOSSY: V_μ≤(4·0.7)^μ V_0=n^{1.485} ⟹ M≤n^{0.74} (provable-if-deficit, beats di Benedetto
  0.989, NOT prize). The multiplicative compounding loses the log-structure.
- C2 reflects TRUE M: M²/n=log q/c, c≈0.7 ⟹ M=n^{0.5}·polylog (PRIZE exponent). Proving=BGK.
- **PRIZE ⟺ the dyadic period histogram {|η_b|²/n} has exponential tail decay with a uniform-in-n
  positive rate c≥c₀>0** (any constant c₀, not just 0.5: M≤√(n log q/c₀)=O(√(n log q))). Measured c≈0.7.
  This is the cleanest distributional form: NOT "rate=1/2" but "rate bounded below" — weaker, but still
  the uniform-in-n Gauss-period equidistribution-tail = BGK. The whole prize is: the n-fold period sum
  is sub-exponential with n-independent rate.

## The period tail rate c — asymptotic (precise fit)
Least-squares fit of #{b:|η_b|²/n>t}/q ~ exp(−c t): c = 0.726, 0.628, 0.586, 0.573 (n=16,32,64,128),
DECREASING toward ~0.5 (=Wick/Gaussian). M²/(n·ln q) = 1.09, 1.18, 1.40 (<2=√2-bound), so the prize
bound M≤√(2n ln q) HOLDS WITH ROOM and the constant approaches √2 from below as n→∞ — consistent with
the robust A_r≤Wick measurement (clean) and with the periods being asymptotically Gaussian (c→1/2).
**Final characterization:** the prize sup-norm M=max_{b≠0}‖η_b‖ for dyadic μ_{2^μ} at p~n^4 satisfies
M=√(c⁻¹·n·ln q) with c→1/2 (Gaussian), i.e. M~√(2n ln q); PROVING c≥1/2−o(1) uniformly in n = the
Gauss-period Gaussian-tail theorem = BGK. The dyadic structure gives c≈0.7 at finite n (C1 deficit /
C2 tail), tightening to the Gaussian 0.5 — the whole open content is this single uniform-tail limit.
/tmp/probe_rate_fit.py.

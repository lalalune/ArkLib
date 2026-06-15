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

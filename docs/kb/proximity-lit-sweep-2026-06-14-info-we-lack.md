# Proximity Prize (#407) — "info-we-lack" literature sweep, 2026-06-14

META-METHOD sweep: identify the exact external mathematical input the program lacks, then survey
the 2025-2026 additive-combinatorics / analytic-NT / proximity-gap literature for any result that
supplies it. Extends the 2026-06-13 Paley/Gauss-period sweep (`proximity-paley-gauss-period-litsweep`).

## The residual (verified, unchanged)
FLOOR side: `max_b |eta_b| <= C sqrt(n log m)` (R3 DFT-flatness) <=> `|mu_n^{(+r)}| <= eps* q` at
`r~log q` (R1) <=> `delta* >= 1 - rho - Theta(1/log n)` (lower bound on delta*). THIN (n<<p^{1/4}),
UNIFORM over primes incl. Fermat, NON-MOMENT. This is an UPPER bound on the sup-norm / bad-set.

## NEW papers found (NOT in prior sweeps) and their precise verdicts

### Proximity-gap face (all CEILING / upper-witness side = delta* <= ...; confirm, don't refute, the residual)
- **Haböck-Krachun-Kazanin, eprint 2026/782 (Apr 2026) "Failure of proximity gaps close to capacity".**
  Haböck = BCHKS framework author. For `theta = 1-rho-eta`, `eta = Theta_rho(1/log n)`, constructs an
  affine line not entirely theta-close but with `2^{Omega_rho(1/eta)} = n^{Omega(1)}` close points,
  via a NEW additive-combinatorics lemma on SUMS OF ROOTS OF UNITY. This is exactly the program's
  CEILING `delta* <= 1-rho-Theta(1/log n)`, now explicit. = the LOWER-bound (existence-of-bad-line)
  direction; OPPOSITE to the residual's needed upper bound. The lemma's proof technique is the freshest
  tool on the exact object (sums of roots of unity) — worth obtaining the PDF for the lemma statement.
- **Crites-Stewart, eprint 2025/2046 (Nov 2025) "On RS Proximity Gaps Conjectures".** MCA/CA/list
  up-to-CAPACITY (delta<1-rho) FALSE via Cantelli/2nd-moment (NOT roots-of-unity). Surviving conj =
  up to LIST-DECODING capacity `H_q(delta)<1-rho` (~3.2% reduction at log q>=31). Already in-tree
  (`ListDecodingConjectureRefutation.lean`, [CS25]).
- **Kambiré arXiv:2604.09724**: explicit bad line at edge (ceiling), quantitative Linnik. Already known.
- eprint 2026/861 (Action-Orbit FRI above Johnson), 2026/858 (FRI via Threshold Halving),
  2025/1712 (Syndrome-Space Lens), 2601.10047 (JLR folded-RS subspace designs): adjacent FRI-soundness
  / folded-code work, not the plain-RS thin-subgroup floor. NOT swept in detail (lower priority).

### Additive-energy / character-sum face (all WRONG REGIME or WRONG DIRECTION for the residual)
- **Hegyvari, arXiv:2602.01781 (Feb 2026) "On the distribution of additive energy revisited".** Fourier
  methods, multiplicative energy E_3^x/E_4^x of sets with small doubling. Thm 5.1 needs `|A| > p^{3/4}/K^{1/4}`
  = FAT. VACUOUS at prize n<<p^{1/4}.
- **Darbar-Kerr-Munsch-Shparlinski, arXiv:2604.02960 (Apr 2026) "Large values of L(sigma,chi) for
  subgroups of characters".** Two relevant pieces, both wrong for the residual:
  (i) Thm 2.7 (mean-value over a character subgroup, builds on Heath-Brown 1979 large sieve):
  `M = (1/A) sum_{chi in A} |sum_{n<=N} alpha_n chi(n)| <= K^{1/2}(N^{1/2}+A^{-1/2}N+A^{-3/8}N^{1/2}q^{1/4}) q^{o(1)}`.
  Under the favorable transfer (N<->n, A<->m=index=2^128) the MEAN bound = `2^15 = sqrt(n)` = the
  Parseval floor (the q^{1/4} term is killed: A^{-3/8} q^{1/4} n^{1/2} = 2^6.5). But it's the MEAN; the
  max can be sqrt(A)=2^64 larger — the L1->Linfty gap is the entire open problem. Heath-Brown Lemma 3.1
  is an L2 large-sieve double sum, no individual sup control. NO sup-norm bound anywhere.
  (ii) resonator/Gal-sum LOWER bounds (Thm 2.1/2.2): prove the MAX is LARGE over thin character
  subgroups — confirms the program's structured-prime obstruction direction, but it's a lower bound.
- **arXiv:2603.12159 (large values of mixed char sums), 2604.02306 (large values of exp sums with
  multiplicative coeffs)**: large-values/resonance over the INTEGERS (magnitude N exp(-c sqrt log N)),
  not finite-field thin subgroups. Conceptually adjacent (resonance machinery), no transfer.
- **arXiv:2603.02118 (incomplete mixed char sums)**: Weil sqrt-q scale, additive translates, not thin
  subgroups. VACUOUS.
- **Sawin "Stratification theorems for exponential sums in families" arXiv:2506.18299 (Jun 2025)**:
  p-uniform for FIXED varieties but bounds scale as p^{dim/2} >= sqrt(p), NOT sqrt(n); subgroup-index
  pushforward complexity grows with k=2^128. Same AG no-go the program proved (Betti exponential).
- **"Equidistribution of exp sums indexed by a subgroup of fixed cardinality" (Camb. Phil. Soc.)**:
  the right regime (fixed-cardinality subgroup) but Sato-Tate / distribution (mean+var), not the
  individual sup-norm uniform in p. Same as Katz equidistribution = wrong quantity.

## NET (HONEST)
NO 2025-2026 paper supplies the residual's needed UPPER bound (thin-subgroup, uniform-in-p sup-norm /
bad-set count). The newest results all push on the LOWER / ceiling side: HKK 2026/782 + Kambiré +
Crites-Stewart now make the CEILING `delta* <= 1-rho-Theta(1/log n)` explicit/proven, exactly matching
the program's proven ceiling — so floor+ceiling would PIN delta* iff the floor is proven up to it. The
residual (floor) survives unchanged; its status is still "Paley Graph Conjecture / optimal thin-subgroup
sum-product" (open everywhere below p^{1/2}). The single freshest actionable artifact is the HKK
"additive-combinatorics lemma on sums of roots of unity" — obtain the PDF (Cloudflare-blocked here) and
check whether it is a tight TWO-SIDED count whose complement bounds the bad set `|mu_n^{(+r)}|`.

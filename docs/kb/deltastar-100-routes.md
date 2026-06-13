# 100+ attack routes on the δ* open core — triaged for the prize regime (#389/#371)

**The target (pinned, exact).** After the Fourier/MacWilliams reduction
`incidence = (q|C|/qⁿ)(|Ball| + 𝒮)`, `𝒮 = Σ_{ξ∈D∖0} K_w(wt ξ)·e(ξ·u₀)`, `D = C^⊥∩u₁^⊥`,
the prize is exactly:

> **(★CORE)** worst-case `|𝒮| ≤ |Ball|`  ⇔  `N(u₀)=#{x∈C+⟨u₁⟩ : wt(x−u₀)≤w} ≤ 2·avg(N)` for all `u₀`
> ⇔ no-concentration / beyond-Johnson list-decoding for the explicit dim-`(k+1)` MDS-derived code
> `C+⟨u₁⟩`, in the **prize regime**: smooth `μ_n` domain, constant rate `ρ∈{1/2,…,1/16}`,
> `n ≪ √q` (`q≈n·2^128`), window radius `δ∈(1−√ρ, 1−ρ−Θ(1/log n))`, `ε*=2^-128`.

Proven facts to respect (any route reducing to these is OUT):
W1 per-witness counting caps at `C(w−1,d+1)` (exhausted); W2 additive energy carries a fatal √-loss
(sub-Johnson); W3 confluent-Stepanov stalls at `n^{2/3}`; W4 the max incomplete character sum is
`Θ(√(n log(q/n)))` — the moment method provably stops one `√(log)` short (`ShawFlatnessRefuted`);
W5 the budget/supply pin lands at `ε*=supply/p`, *above* the window. L² average holds
(`E_{u₀}|𝒮|²=Σ K_w²`); the gap is the worst-`u₀` `√(log)` excess.

**Legend.** ✗J reduces to Johnson/UDR · ✗triv triviality · ✗inc needs open NT/GRH/incomputable
input · ✗W# hits proven wall # · ~sm small-subgroup only (`n<log p`, not deployed) · ★ genuinely
worth trying / not obviously dead.

---

## A. Exponential / character sums
1. Weil bound on `𝒮` per frequency — ✗W4 (`√q` completion vacuous for `n≪√q`).
2. BGK (Bourgain–Glibichuk–Konyagin) sum-product cancellation `n^{1−ε}` — ✗inc (ε too small; not √-sharp; the named open Prop).
3. Bourgain's `exp(−c·t)` for subgroups of size `q^δ` — ✗inc (constant `c` unquantified at the prize δ).
4. Heath-Brown / Konyagin incomplete-Gauss-sum bounds — ✗W4 (give `√q`, not `√(n log)`).
5. Gauss-period closed form (`η_b` = period of `μ_n`) — ✗inc (period magnitudes = open simultaneous-cancellation).
6. Kloosterman/Salié twist of the syndrome character sum — ✗J (curve-genus → Johnson radius only).
7. Vinogradov mean-value / efficient congruencing on the `e(ξu₀)` phases — ✗triv (no multiplicative structure in `u₀`).
8. Postnikov / van der Corput on the Krawtchouk phase — ✗triv (Krawtchouk weight has no smooth phase to difference).
9. Burgess on short intervals of the smooth domain — ✗J (Burgess gives `q^{1/4}`-type, past-Johnson but not capacity).
10. Stationary-phase / oscillatory-integral analogue over `F_q` — ✗triv (no archimedean phase).
11. Bilinear (type-II) decomposition of `𝒮` over `D` — ★ split `D` as `A·B` (subcode factorization) and seek a bilinear Cauchy–Schwarz gain; first step: does RS-dual ∩ hyperplane factor?
12. Karatsuba's double-sum method for incomplete sums — ✗W4 (same `√q` ceiling).

## B. Polynomial method
13. Stepanov auxiliary polynomial vanishing at all bad γ — ✗J (the in-tree `weil_stepanov_card_lt` = Johnson).
14. Confluent Stepanov with Hasse-derivative multiplicities — ✗W3 (stalls at `n^{2/3}`).
15. Guruswami–Sudan interpolation for `C+⟨u₁⟩` — ✗J (GS = Johnson radius exactly).
16. Guruswami–Rudra folded/multiplicity capacity — ✗J for *plain* RS (needs folding; the prize is unfolded).
17. Croot–Lev–Pach / slice rank on the bad-γ set — ✗triv (slice rank bounds cap-sets, gives `o(q)` not `≤n`).
18. Tao's symmetric slice-rank for the 3-tensor of agreements — ✗triv (same).
19. Polynomial partitioning of the syndrome ball — ✗triv (Guth–Katz is archimedean-incidence).
20. Resultant / elimination on the divided-difference ratio map `γ_S=−Q₀[S]/Q₁[S]` — ~sm (the small-subgroup resultant route; `n<log p` only).
21. Wronskian rank-drop at rep points — ✗W3 (the confluent-Stepanov input).
22. Dvir-style Kakeya polynomial bound on far directions — ✗triv (wrong incidence geometry — variety not ball).
23. Multiplicity Schwartz–Zippel for the list polynomial — ✗J (Johnson again).

## C. Additive combinatorics
24. Additive-energy `E(μ_n)≤n^{2+o(1)}` ⟹ list bound — ✗W2 (√-loss: even `E=n²`→ list `n^{3/2}`, sub-Johnson).
25. Higher energies `E_r` via the moment ladder — ✗W2 (same √-loss at every rung; `→√q` only).
26. Plünnecke–Ruzsa on `μ_n` sumsets — ✗triv (subgroup is already sum-closed-ish; no gain).
27. Balog–Szemerédi–Gowers to extract structured bad-γ set — ✗triv (gives structure, not the count `≤n`).
28. Sidon-set / `B_h` bound on `μ_n` — ~sm (proven `μ_n` Sidon for `p>2^n`; deployed `n≫log p` open).
29. Sárközy / Gowers-norm control of the agreement indicator — ✗inc (`U^k`-norm of the code indicator = open).
30. Croot–Sisask almost-periodicity of `1_C * 1_Ball` — ★ extract a Bohr-set of `u₀` where `N(u₀)` is almost-constant; first step: is the Bohr set large enough to force the worst-case?
31. Sanders' quasi-polynomial Bogolyubov on `C+⟨u₁⟩` — ✗triv (Bohr structure too weak for `≤2·avg`).
32. Schoen–Shkredov higher-energy refinements — ✗W2.
33. Subgroup-sumset (BCHKS25 Conj 1.12) — ✗inc (named open conjecture; ~Mersenne).

## D. Coding theory
34. MacWilliams transform of `wt`-distribution of `D` — ★ (it gives the *exact* `𝒮`-without-phase; phased version is the core — see route 30/57).
35. MDS weight enumerator of `C+⟨u₁⟩` — ✗triv (`C+⟨u₁⟩` need not be MDS; even if, enumerator ≠ list count at a *point*).
36. Deep-hole classification of RS (Cheng–Murray, Zhu–Wan) — ★ explicit worst `u₀` = deep hole; first step: are smooth-domain deep holes concentration points? (probe).
37. Covering-radius / list-decoding-radius bracket — ✗J (covering radius = capacity, but the *count* there is the open part).
38. Generalized Hamming weights of `C+⟨u₁⟩` — ✗triv (controls subcode supports, not point list-size).
39. Roth–Lempel / Schur-product structure of RS — ✗triv.
40. Twisted RS / subfield-subcode descent — ~sm (subfield route is the small-subgroup census).
41. List-recovery (CZ25 subspace-design) input — ✗inc (the `CZ25CoordFiberCap` named residual is open for plain RS).
42. GG25 curve-decodability ⟹ MCA — ✗inc for plain RS (proven only FRS/random; the in-tree GAP).
43. Johnson-bound improvement via second-order agreement — ✗J (still Johnson family).
44. Average-radius / Blinovsky list-size bounds — ✗J (asymptotic capacity list-size, not the explicit count).
45. Elias–Bassalygo on `C+⟨u₁⟩` — ✗J.

## E. Fourier / spectral / hypercontractivity
46. Hypercontractivity (Bonami–Beckner) on `1_C` — ✗triv (`q`-ary HC gives `L^p` not the max).
47. KKL / influence bound on the agreement function — ✗triv (no monotone structure).
48. Restriction/extension (Stein–Tomas analogue) for the Krawtchouk transform — ★ `ℓ²→ℓ⁴` restriction of `K_w` to `D` could give the `√` cancellation; first step: is `D` a "restriction-good" subcode?
49. Spectral gap of the Cayley graph `Cay(F_q^+, μ_n)` (the Shaw operator) — ✗W4 (gap = `max|η_b| = Θ(√(n log))`, not flat).
49b. Higher Cheeger / improved-mixing of the same graph — ✗W4 (mixing time controlled by the same gap).
50. Bohr-set / Bourgain restriction on the dual code support — ★ (variant of 48/30).
51. Tensor power trick on `𝒮^t` to amplify cancellation — ✗W4 (amplifies the `√(log)` too; `ShawFlatnessRefuted` shows the moment ladder caps it).
52. Entropy / Shearer on the agreement set distribution — ✗triv (gives volume = average, not max).
53. Talagrand / chaining bound on `sup_{u₀}|𝒮|` — ★ the worst-`u₀` excess is exactly a Gaussian-process supremum; chaining gives `√(log)` — **the prize needs the √(log) to be ABSORBED, so chaining alone reproduces W4** — ✗W4, *unless* the chaining metric on `u₀` is structured by RS (first step: compute the chaining entropy of the `u₀`-process for the smooth code).
54. Generic chaining / majorizing measures (Talagrand) on the RS-structured index — ★ (the refined version of 53; the RS structure might shrink the entropy below `log q`).

## F. Algebraic geometry
55. Hasse–Weil on the agreement curve — ✗J (genus → Johnson).
56. Étale cohomology / `ℓ`-adic sheaf bound (Katz) for the family `𝒮(u₀)` — ★ if `𝒮(u₀)` is a trace function of a *geometrically irreducible* sheaf of bounded conductor, Deligne gives `√`-cancellation uniformly in `u₀`; first step: is `u₀↦𝒮` a trace function? (conductor = ? for the Krawtchouk-weighted dual-code sum).
57. Katz's "sums of products" / Krawtchouk-as-trace-function — ★ Krawtchouk polynomials ARE trace functions (Kloosterman-type); express `𝒮` as a sum of a trace function over the subcode and apply Fouvry–Kowalski–Michel; first step: identify the sheaf.
58. Curve over `F_q` for the divided-difference ratio variety — ✗J.
59. Weil II / vanishing cycles on the syndrome variety — ✗inc (sheaf irreducibility = the open input).
60. Drinfeld modular / function-field analogue — ✗triv (no modular structure here).
61. Lang–Weil point count on `{N(u₀)≥t}` — ✗triv (variety dimension gives volume, not the sharp count).

## G. Probabilistic / second moment
62. Second moment `E_{u₀}|𝒮|²=Σ K_w²` + Chebyshev — ★ proven; gives typical bound; **worst-case needs more** (the open gap). Landable in Lean (the one I offered).
63. Fourth moment of `𝒮` over `u₀` — ✗W4 (4th moment → `√(log)` excess, same as W4).
64. `2k`-th moment ladder of `𝒮(u₀)` — ✗W4 (moment method caps at `√(log)`; `ShawFlatnessRefuted`).
65. Azuma/McDiarmid on `N(u₀)` as a martingale in coordinates — ✗triv (bounded differences give `√n·√n`, too weak).
66. Talagrand concentration of `N(u₀)` — ✗triv (concentration around mean ≠ max ≤ 2·mean; the rare structured `u₀` escapes).
67. Janson / Suen for the dependency graph of agreements — ✗triv.
68. Lovász Local Lemma to forbid a concentration `u₀` — ✗triv (dependencies too dense).
69. Spencer / partial-coloring derandomization of `u₀` — ✗triv.

## H. Number theory
70. GRH-conditional Montgomery–Vaughan large sieve on `η_b` — ✗inc (conditional on GRH; not unconditional).
71. Large sieve inequality for the smooth-domain frequencies — ✗W4 (large sieve = `√(N·(N+Q))`, recovers L²-average only).
72. Multiplicative-energy / Heilbronn-sum bounds — ✗inc.
73. Polya–Vinogradov for the multiplicative character twist — ✗J (`√q log q`, past-Johnson not capacity).
74. Sub-Polya–Vinogradov (Granville–Soundararajan) for smooth subgroups — ✗inc (GRH-regime).
75. Gallagher's larger sieve on the bad-γ set — ✗triv (sieve counts residues, not list-size).
76. Erdős–Ko–Rado / Frankl on the intersecting agreement sets — ✗W1 (this IS the per-witness packing).
77. Sidon/Singer difference-set structure of `μ_n` — ~sm.
78. Distribution of `μ_n` in Bohr sets (Bourgain) — ✗inc.

## I. Incidence geometry
79. Szemerédi–Trotter over `F_q` (Bourgain–Katz–Tao) — ✗triv (point-line incidence ≠ ball-line).
80. Elekes–Rónyai for the ratio map — ✗triv (gives expansion, not the count).
81. Kakeya/Nikodym in `F_q^{n−k}` for the line family — ✗triv (lines vs weight-balls mismatch — W4 note).
82. Furstenberg-set / `(s,t)`-set bound on the syndrome lines — ✗triv.
83. Rudnev's point-plane incidence — ✗triv.

## J. Representation theory / association schemes
84. Delsarte LP bound on the dual-code distance distribution — ★ LP gives the *exact* extremal weight distribution of `D`; feeding it into `𝒮` (route 34) could bound the *phaseless* sum — but the phased core remains (still needs cancellation) — ✗triv for the phased version.
85. Terwilliger algebra of the Hamming scheme — ★ the Krawtchouk-weighted sum over a subcode is a Terwilliger-module object; first step: does the subcode `D` sit in a low-dim Terwilliger module giving an operator-norm bound?
86. Gelfand-pair zonal spherical functions — ✗triv (= Krawtchouk, already used).
87. MacWilliams duality as a `GL` intertwiner — ✗triv (= MacWilliams).
88. Association-scheme eigenvalue (Bannai–Ito) bound — ✗W4 (eigenvalues = Krawtchouk = the same).

## K. Subspace designs / pseudorandomness
89. Subspace-design list-recovery (Guruswami–Xing) — ✗inc (the CZ25 input; open for plain RS).
90. Dimension expander / lossless from RS derivative code — ✗triv.
91. Pseudorandom-generator fooling the ball test — ✗triv (would need the code to ε-fool, = the prize).
92. Extractor / Trevisan-style from the RS code — ✗triv (extractor property = the cancellation).
93. ε-biased-set characterization of `C+⟨u₁⟩` — ★ the prize ⇔ `C+⟨u₁⟩` is `(ε*)`-biased against the ball test; first step: is the smooth RS dual an explicit small-bias set at the window weight? (this is the cleanest restatement; the bias = `𝒮/|Ball|`).

## L. Folding / structural
94. Fold `μ_n` by the 2-adic tower, transport capacity — ✗J (Chen–Zhang unfolding loss; the in-tree vector-5 GAP).
95. Tensor RS = bivariate, use Schwartz–Zippel — ✗J.
96. Interleaved-RS / simultaneous list-decoding (the MCA stack itself) — ✗J (MCA δ*=LD δ*, the in-tree separation).
97. Derivative/Hasse code descent — ✗W3.
98. Frobenius-orbit averaging of the bad set (equivariance) — ~sm (A5 equivariance pin; doesn't reach window).

## M. Computational / explicit
99. `decide`/native exact list-count at one deployed prime — ✗inc (`q=2^128`, infeasible; `native_decide` banned).
100. Probe extrapolation of `max 𝒮/|Ball|` vs `q` to the prize — ✗inc (small-`q` saturation; can't reach `2^128`).
101. Verify `C+⟨u₁⟩` bias for a specific NTT prime via Gauss-sum identities — ✗inc (per-prime resultant coincidence).
102. SAT/SMT search for a concentration `u₀` at small scale — ✗inc (small-scale only; no asymptotic transfer).

## N. Hybrid / cross-cutting (the genuinely-live shortlist)
103. ★ **Sheaf-trace (56+57) × generic-chaining (54):** if `u₀↦𝒮` is a trace function of bounded conductor, Deligne gives a *uniform* `√q`-type bound, and the RS-structured chaining entropy may convert `√q` into the needed `√(n log(q/n))` over the relevant `u₀`-family. This is the only route that could beat W4 without GRH — it imports Katz's machinery (never applied to the Krawtchouk-weighted *subcode* sum). First step: write `𝒮(u₀)` as `Σ_{ξ∈D} (trace fn)(ξ) e(ξu₀)` and compute the sheaf's conductor.
104. ★ **ε-biased restatement (93) × Delsarte-LP (84):** prove the smooth RS dual is an explicit small-bias set at window weight by an LP/Terwilliger operator bound — sidesteps character sums entirely. First step: set up the Delsarte LP for `D` at radius `w` and check the dual feasible point gives `≤ |Ball|`.
105. ★ **Croot–Sisask (30) × deep-holes (36):** almost-periodicity confines concentration to a Bohr set; deep-hole classification enumerates the only candidate concentration `u₀`; check those finitely-structured points directly. First step: do RS deep holes lie in the Croot–Sisask Bohr set?
106. ★ **Bilinear (11) × Terwilliger (85):** factor `D` and apply an operator-norm bound in the Terwilliger module. First step: the factorization.
107. ✗ moment/energy hybrids (24/25/51/62-64) — all ✗W2/W4 (the √-loss / √-log wall is route-invariant).
108. ✗ Stepanov/Weil/GS hybrids (13-16/55) — all ✗J (Johnson-invariant).

---

## Verdict tally (≈108 routes)
- **✗J (Johnson/UDR-bound):** 13,15,16,23,37,42,43,44,45,55,58,73,94,95,96,108 — the whole "improve-Johnson" family is structurally capped below the window.
- **✗W2/W3/W4 (energy/Stepanov/char-max walls):** 1,4,5,14,21,24,25,32,49,49b,51,63,64,71,88,97,107 — every moment/energy/spectral route stops at `√q` or `√(log)`-short.
- **✗triv:** 6-10,17-19,22,26,27,31,35,38,39,46,47,52,60,61,65-69,75,79-83,86,87,90,91,92 — gives volume/structure, never the sharp `≤2·avg` count.
- **✗inc (open-NT/GRH/conjectural input):** 2,3,29,33,41,59,70,72,74,78,89,99,100,101,102 — reduces to a *different* recognized open problem.
- **~sm (small-subgroup only, not deployed):** 20,28,40,77,98 — proven where `n<log p`; the deployed `n≫log p` is the open part.
- **★ GENUINELY LIVE (never-tried, not obviously dead):** 11 (bilinear factorization), 30 (Croot–Sisask), 34 (phased MacWilliams), 36 (deep-hole concentration), 48/50 (Krawtchouk restriction), 53/54 (generic chaining on RS-structured `u₀`), 56/57 (**sheaf-trace / Katz**), 62 (second moment — landable now), 84/85 (Delsarte-LP / Terwilliger operator), 93 (**ε-biased restatement**), 103-106 (the hybrids).

**The single most promising never-tried direction:** routes **56/57/103 (Katz sheaf-trace)** and **93/104 (ε-biased / Delsarte-LP operator)** — the only two families that could give worst-case `√`-cancellation *without* assuming the open BGK/GRH character-sum bound, because they bound `sup_{u₀}|𝒮|` by an algebraic conductor or an LP dual certificate rather than by moments (which provably stop `√(log)` short, W4). Everything else collapses to Johnson, a proven wall, a triviality, or a different open problem.

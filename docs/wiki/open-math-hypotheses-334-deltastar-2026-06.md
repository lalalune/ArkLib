# Open-math hypotheses for #334 (δ* residuals, Johnson↔capacity) — 2026-06-10

Companion to [`open-math-hypotheses-2026-06.md`](open-math-hypotheses-2026-06.md) (which covers
the #301/#302/#304 kernels). This ledger covers issue #334: the δ* window for mutual correlated
agreement (MCA) of explicit smooth-domain RS codes, and the formalizable residuals B1–B4.

Literature swept end-to-end for this ledger (2026-06-10): [Jo26] ePrint 2026/891 (full proof of
Thm 4.2/4.4/Cor 4.5, Lemma 3.1/3.2/4.1, §5 curve decodability, read from the PDF), [KKH26]
ePrint 2026/782 (Lemma 1 resultant argument, the Stirling step, Lemma 2 / Thorner–Zaman
[TZ24, Cor 3.1] short-interval PNT in APs with smooth moduli, Appendix-A route with c = H₂(ρ)),
[ABF26] 2026/680, [BCGM25] 2025/2051 (MCA at Johnson for all polynomial generators), Haböck
2025/2110, [BCHKS25] 2025/2055 / ECCC TR25-169 (zero-loss to Johnson; Ω(n^1.99)-exception lower
bounds; CA⇒LD reduction item 5), [CS25] 2025/2046 (capacity conjectures disproved; CA⇒LD),
[GG25] 2025/2054 (curve decodability; FRS/subspace-design at capacity), JLR arXiv:2601.10047,
Kambiré arXiv:2604.09724 (companion of KKH26), [CHK25] ECCC TR25-170 (deterministic Johnson
list decoding), Chai–Fan 2026/858 + 2026/861 (protocol tricks / conditional — not edge-movers),
MW26 2026/1055 (consumes MCA), plus the random-RS capacity line (BGM/GZ/AGL — ensemble-only,
no derandomization as of June 2026).

**Window state (post-sweep verdict):** lower edge = Johnson 1−√ρ, now held by *full MCA*
(BCGM25/Hab25), not just CA; upper edge = 1−ρ−Θ_ρ(1/log n) (KKH26/Kambiré) for smooth
prime-field domains; both edges genuinely open in between; CS25/BCHKS25 couple any
below-edge progress to beyond-Johnson list decoding of explicit RS (≈25 years open).
In-tree bracket engine ready (`MCAThresholdLedger`, `KKH26WitnessSpread`,
`InterleavingStabilityMCA`, `EpsMCAInterleavedList`, `MCAWitnessSpread`).

Per-hypothesis discipline: constraints → new direction → why nobody has done it → larp-check
(have they actually?) → what is novel → the hypothesis → proof plan.

## Known-grounded hypotheses

### K1 — `epsMCAP` interleaving exactness (Jo26 Thm 4.4/Cor 4.5 for the in-tree power generator)
- **Constraints**: in-tree exactness (`epsMCA_interleaved_eq`) is affine-line/`Fin 2` only;
  the in-tree `epsMCAP` (general `parℓ`, exponents `exp`, seed `γ ← F`) has NO interleaving
  theorem; `jointPairSubmodule` is hardcoded to pairs.
- **New direction**: the seed space of `epsMCAP` is `F` itself (|Ω| = q ≤ q), so [Jo26]
  Thm 4.4 applies: EXACT equality, no factor. The covering lemma
  `exists_nonzero_notMem_of_proper_family` is already in-tree and is exactly [Jo26] Lemma 3.2.
- **Why nobody has done it**: `epsMCAP` landed for WHIR plumbing (#302 lane) after
  `InterleavingStabilityMCA` was written; nobody connected them.
- **Larp-check**: this IS [Jo26] Corollary 4.5 — known math, not new. (Earlier draft of this
  hypothesis guessed exactness generalizes; the paper already says so. Honest status:
  formalization-only novelty.) Probe `probe_jo26_interleaved_generator_factor.py`: equality
  observed at every exhaustive instance including t=3 power stacks.
- **Novel**: first formalization; subsumes issue #334's B1 *for the power generator* (the
  factor bound follows trivially from equality since A(q,s) ≥ 1).
- **Hypothesis**: `epsMCAP_interleaved_eq : epsMCAP (C^⋈ (Fin s)) exp δ = epsMCAP C exp δ`
  for `C : Submodule`, any `parℓ`, `exp`, `s ≥ 1`.
- **Proof plan**: generalize `jointPairSubmodule` to `parℓ`-tuples (`jointTupleSubmodule`,
  same add/smul proofs summed over `j : Fin parℓ`); properness by standard-basis vectors
  (mirrors `jointPairSubmodule_ne_top`); both directions mirror
  `epsMCA_le_epsMCA_interleaved` / `epsMCA_interleaved_le_epsMCA` with `curveComb` in place
  of the affine line (the key identity `λ·(∑ⱼ γ^{exp j} Uⱼ) = ∑ⱼ γ^{exp j} (λ·Uⱼ)` is
  bilinearity, exactly as in the line case).

### K2 — The generator abstraction + [Jo26] Thm 4.2 factor by finite double counting (B1 proper)
- **Constraints**: B1 as stated in #334 is for ARBITRARY coefficient generators
  `G : Ω → F^ℓ` (arbitrary finite seed set); no generator abstraction exists in-tree; the
  paper's proof averages over uniform nonzero λ — but everything is finite.
- **New direction**: replace the probabilistic averaging by pure `Finset.card` double
  counting: #{(ω,λ) ∈ B × (F^s∖0) : λ ∉ K_ω} ≥ |B|·q^{s−1}(q−1) (Lemma 3.1 as a cardinality
  bound per row), so some λ-column has ≥ |B|·q^{s−1}(q−1)/(q^s−1) preserved bad seeds —
  pigeonhole, no measure theory.
- **Why nobody has done it**: the paper is 4 weeks old; no formalization exists anywhere.
- **Larp-check**: proof transcribed in full from the PDF (agent digest 2026-06-10); the
  geometric series is ONLY the closed form of (q^s−1)/(q^{s−1}(q−1)) — there is no s-level
  union; transcription risk low.
- **Novel**: first formalization of generator-MCA (ε_G) and of Thm 4.2; the `Finset` recast
  of the averaging step.
- **Hypothesis**: with `epsMCAGen (G : Ω → F^ℓ) C δ` defined as sup over `ℓ`-stacks of the
  fraction of bad seeds, both `epsMCAGen_le_interleaved` and
  `epsMCAGen_interleaved_le_factor : ε_G(C^{≡s}) ≤ A(q,s)·ε_G(C)` formalize, with
  `A(q,s) = (q^s−1)/(q^{s−1}·(q−1))`, plus `epsMCAGen_interleaved_eq` when `|Ω| ≤ q`.
- **Proof plan**: Lemma 4.1 (one proper `K_ω` per bad seed: puncturing commutes with
  interleaving — rowwise membership; properness by basis vectors); cardinality Lemma 3.1
  (`K.toFinset.card ≤ q^{s−1}` for proper submodules of `F^s`); double count; bridge lemmas
  to `epsMCA` (ℓ=2, Ω=F, G=(1,γ)) and `epsMCAP`.

### K3 — KKH26 entropy form: the ceiling at η = Θ(1/log n) via the method-of-types bound (B3a)
- **Constraints**: in-tree `kkh26_mcaDeltaStar_le` is exact-count form (`2^r·C(2^{μ-1},r)`);
  the paper's Theorem-1 phrasing needs `log₂ C(s/2,r) = (s/2)H₂(2r/s)(1−o(1))` and the
  n-vs-s sandwich `½·2^{cs/τ} < n ≤ 2^{cs/τ}`; Mathlib has `Real.binEntropy` and Stirling
  (`Real.Stirling`), but the needed type bound `C(n,k) ≥ 2^{n·H₂(k/n)}/(n+1)` must be located
  or proven.
- **New direction**: skip asymptotics-as-limits; prove the EXPLICIT inequality chain
  `2^r·C(s/2,r) ≥ 2^{r + (s/2)·H₂(2r/s) − log₂(s/2+1)}` (method of types), then the finite
  sandwich corollary: for the KKH26 family with the paper's parameter choices, the bad-scalar
  count is ≥ n^{τ−o(1)} expressed as an explicit finite inequality in (s, τ, c) — every
  consumer of "Θ(1/log n)" gets a quantified statement, no filters/limits needed.
- **Why nobody has done it**: asymptotic phrasings repel formalizers; the explicit-constant
  form is new bookkeeping nobody in the paper needed.
- **Larp-check**: the type bound is classical (Cover–Thomas Lemma 2.3 / "method of types");
  Mathlib status of `choose_le_two_pow_mul`-style entropy bounds unverified — the agent must
  search Mathlib first and prove from `Nat.choose` + `Real.rpow` if absent.
- **Novel**: first formal entropy-form ceiling for the prize window; unlocks the η-phrasing
  rows of the issue's reach table.
- **Hypothesis**: `kkh26_count_entropy_lb : (2^r * (s/2).choose r : ℝ) ≥
  2^(r + (s/2)*binEntropy(2r/s)/log 2 − Real.logb 2 (s/2+1))` (shape up to the agent), and the
  consumer `kkh26_eta_form` restating `kkh26_mcaDeltaStar_le` with radius
  `capacity − 2/s` and count `≥ 2^{s(c−o(1))}` made explicit.
- **Proof plan**: `C(n,k)·(n+1) ≥ 2^{nH(k/n)}` from `∑ C(n,j)x^j(1-x)^{n-j} = 1` at
  `x = k/n` (the max term is C(n,k)x^k(1-x)^{n-k} and there are n+1 terms); then pure algebra.

### K4 — Thorner–Zaman as a named external + KKH26 Lemma 2 good-prime counting (B3b)
- **Constraints**: in-tree `kkh26_*` need `p > (2^μ)^{2^{μ-1}}` ((s/2)·μ bits) — the probe
  table shows the ε* = 2^{-128}, |F| < 2^256 windows are EMPTY for s ≥ 64; the paper fixes
  this with p = Θ(n^β) via [TZ24, Cor 3.1] (short-interval PNT in APs, smooth moduli,
  exponent 7/12 ⟹ β > 12/5) — deep analytic number theory, NOT formalizable this decade.
- **New direction**: isolate TZ as a NAMED HYPOTHESIS structure (never an axiom) carrying
  exactly the counting interface the proof consumes (≥ Ω(n^{β−1−o(1)}) primes ≡ 1 mod n in
  [n^β, 2n^β]); prove KKH26 Lemma 2 (good-prime existence avoiding all ≤ a² resultant
  divisors, each resultant ≤ s^{s/2} hence ≤ (s log s)/(2β log n) large prime factors) as
  pure finite counting GIVEN the interface; conclude the conditional polynomial-field-size
  ceiling.
- **Why nobody has done it**: the analytic input scared everyone off; but the *reduction* is
  elementary and it's the reduction that the issue's B3 actually needs.
- **Larp-check**: TZ24 is real (Thorner–Zaman, "Refinements to the prime number theorem in
  arithmetic progressions", Cor 3.1 per the paper's citation); the in-tree hypothesis-bundle
  pattern (Hab25Johnson-style structures, "no field is sorry/axiom") is the established
  vehicle.
- **Novel**: the formal reduction TZ-interface ⟹ s ≥ 64 windows open; an exact price tag on
  the analytic input (which rows of the reach table it buys).
- **Hypothesis**: `structure TZPrimeSupply` (the counting interface) +
  `kkh26_good_prime_of_TZ : TZPrimeSupply → ∃ p ∈ [n^β, 2n^β], p ≡ 1 [MOD n] ∧ GoodRes p` +
  conditional ceiling `kkh26_mcaDeltaStar_le_poly_field`.
- **Proof plan**: resultant size bound already in-tree shape (`kkh26_lemma1`'s inequality
  (3)); prime-factor count `Ω(N) ≤ log N / log(n^β)`; union over ≤ a² pairs; compare with
  the supplied prime count; instantiate the in-tree bracket.

### K5 — Curve decodability ([GG25] Def 3.1) + the marked equivalence and interleaving transfer ([Jo26] §5) (B2 opener)
- **Constraints**: B2 needs [GG25] Def 3.1 from scratch; [Jo26] §5 gives the transfer
  theorems (5.5 marked⟺original, 5.7 exact preservation when C(a,b) ≤ q, 5.8 weighted);
  the covering lemma is in-tree; the per-B-subset subspace `V_B` is new.
- **New direction**: formalize *marked* curve decodability (Def 5.1) FIRST — it is the
  version with the subspace structure — and get the [GG25] form via Thm 5.5; the transfer
  5.7 then reuses `exists_nonzero_notMem_of_proper_family` verbatim (C(a,b) ≤ q subspaces).
- **Why nobody has done it**: GG25 is for folded-RS/subspace-design codes — a different code
  family from the in-tree RS focus; nobody needed the definition until Jo26 §5 made it
  transfer-relevant.
- **Larp-check**: full statements transcribed from the PDF (Def 2.7, 5.1, Lemma 5.2/5.4/5.6,
  Thm 5.5/5.7/5.8); no formalization exists anywhere.
- **Novel**: first formalization of curve decodability; the interleaving transfer makes any
  future GG25-style capacity result for explicit codes immediately interleaving-stable
  in-tree.
- **Hypothesis**: `CurveDecodable C ℓ δ a b` (GG25) and `MarkedCurveDecodable` formalize;
  `marked_iff` (5.5, needs `b ≤ a ≤ q`); `curveDecodable_interleaved` (5.7, needs
  `(a.choose b) ≤ q`).
- **Proof plan**: Lemma 5.2 (interpolation for b ≤ ℓ+1); Lemma 5.4 (redefine f off A₀ to be
  δ-far — needs a non-covering counting condition); Lemma 5.6 (row-combination projection
  monotone in disagreement sets); V_B subspace + basis-vector properness + covering.

## Advanced hypotheses (new math)

### A1 — The seed-size dichotomy is hollow: exactness beyond |Ω| ≤ q
- **Constraints**: [Jo26] Thm 4.4 needs |Ω| ≤ q because q+1 proper subspaces CAN cover F_q^s
  (the q+1 lines of F_q²); Thm 4.2 pays A(q,s) for general Ω; Remark 4.3 shows sharpness only
  of the AVOIDANCE STEP, not of the theorem.
- **New direction**: a violating instance needs |Ω| > q witnesses whose bad-seed subspaces
  K_ω actually REALIZE a covering family — but K_ω are not arbitrary: they are joint-agreement
  subspaces of one fixed stack, heavily correlated through the code. Probe
  `probe_jo26_multiseed_exactness.py`: at |Ω| = q² (generator (a,b) ↦ (1,a,b)), the ratio is
  EXACTLY 1.000 on every instance measured (exhaustive at RS[F₃,2,1], RS[F₅,2,1];
  diag+sampled at RS[F₅,4,2]). Either exactness extends well beyond |Ω| ≤ q, or the sharp
  instance needs adversarial generators.
- **Why nobody has done it**: the paper is 4 weeks old and stops at the clean dichotomy; the
  correlation structure of {K_ω} is untouched territory.
- **Larp-check**: Jo26 Thm 4.7 pays Σᵢ ε_{H_i} for polynomial generators — strictly worse
  than equality — so the paper does NOT contain this; genuine novelty risk is inverse
  (it may be FALSE for adversarial G; the exhaustive-generator search below decides).
- **Novel**: either a new theorem strictly improving Jo26 Thm 4.2 for structured generators,
  or the first sharp instance showing the factor is real.
- **Hypothesis**: for every coefficient generator (any finite Ω) and every F_q-linear C,
  ε_G(C^{≡s}, δ) = ε_G(C, δ). Fallback (if adversarial search refutes): exactness holds for
  all generators with AFFINE seed-to-coefficient structure (products of ≤ q-seed coordinate
  maps), via an iterated/slice-wise covering argument.
- **Proof plan**: probe: exhaustive search over ALL generators G : Ω → F₃² with |Ω| = 4,5 on
  RS[F₃,2,1] (9^|Ω| generators — feasible) hunting ratio > 1; if none, attempt the proof: the
  K_ω family of one stack lies in the image of S ↦ jointTupleSubmodule(S), bounded by the
  number of distinct witness sets — if the DISTINCT subspaces among {K_ω} number ≤ q,
  Lemma 3.2 applies regardless of |Ω| (key question: can one stack realize > q distinct
  joint-agreement subspaces?).

### A2 — The KKH26 spread count is not tight: antipodal-pair classes via the in-tree de Bruijn classification
- **Constraints**: KKH26 Lemma 1 counts only S ⊆ G with S ∩ (−S) = ∅ (sign-free
  sum-polynomials), giving 2^r·C(s/2,r); subsets WITH antipodal pairs produce sums of
  smaller support — collisions are governed by vanishing sums of roots of unity; for
  s = 2^b the in-tree de Bruijn machinery (#232 lane, `DeBruijnTwoPrimeAssembly` etc.)
  classifies exactly which sub-sums vanish (antipodal pairs only, at prime powers).
- **New direction**: count ALL r-subsets' sums exactly: each S decomposes as (antipodal
  pairs) ⊔ S′ with S′ sign-free; pairs contribute 0; so the sum-multiset is the union over
  r′ = r−2j of the sign-free counts — the distinct-sum count becomes
  Σ_j #distinct(r−2j) ≥ 2^r·C(s/2,r) + 2^{r−2}·C(s/2,r−2) + … STRICTLY exceeding the paper's
  count (the r−2j strata are distinct values by the same resultant argument applied across
  strata, since cross-stratum collisions are also bounded-norm resultants).
- **Why nobody has done it**: KKH26 didn't need it (any 2^{Ω(s)} suffices for Θ(1/log n));
  the cross-stratum distinctness needs the vanishing-sum classification, which exists only
  in this repo.
- **Larp-check**: paper's Remark 2 recasts via norms but keeps S ∩ (−S) = ∅; no stratified
  count in the paper; risk: cross-stratum resultants might need p > (larger threshold) —
  must be tracked exactly.
- **Novel**: a strictly larger machine-checked spread (bigger numerator in
  `kkh26_epsMCA_lower_bound`), hence a strictly stronger in-tree ceiling at the same field
  sizes — cross-lane unification (#232 machinery consuming #334's target), exactly the
  "interpolate parts of the code" win.
- **Hypothesis**: for p > s^{s/2} (same threshold), the number of distinct r-element sums
  from G is ≥ Σ_{j=0}^{⌊r/2⌋} 2^{r−2j}·C(s/2, r−2j) (with the j-th stratum needing
  C(s/2, j) ≥ 1 pairs available, adjust binomials), and the in-tree lower bound numerator
  upgrades accordingly.
- **Proof plan**: probe first (exact arithmetic, small s = 8, 16: enumerate all r-subsets,
  count distinct sums, compare both formulas); if confirmed, formalize the stratified count
  on top of `kkh26_lemma1`'s existing resultant infrastructure.

### A3 — Opening s = 64 unconditionally: certified resultant maxima instead of s^{s/2}
- **Constraints**: the s ≥ 64 reach-table rows are empty because the worst-case bound
  |Res(P−Q, Φ_s)| ≤ (2r)^{s/2} ≤ s^{s/2} sets the prime threshold; the TRUE maximum over the
  needed pairs is plausibly far smaller (O129-style exact-norm computations found maxima
  ~10²⁴ where worst-case bounds were astronomically larger); Parseval/AM-GM gives only
  (4r)^{s/2} (worse), so cheap analytic improvement is blocked — this is genuinely about
  certified computation or new structure.
- **New direction**: the relevant R = P−Q are ±1-coefficient polynomials with ≤ 2r terms
  supported on [0, s/2); their norms ∏|R(ζ)| over primitive s-th roots are resultants of
  LACUNARY polynomials — Myerson/Lenstra-style bounds for lacunary cyclotomic norms, or a
  branch-and-bound certified maximum over the (huge but structured) family via the
  multiplicative structure (R determined by its support multiset mod the rotation action —
  the #232 orbit machinery again).
- **Why nobody has done it**: KKH26 needed only existence; nobody has a reason to care about
  the exact threshold except this repo's ε* = 2^{-128} reach table.
- **Larp-check**: Myerson ("Norms of products of sines...") and the Lehmer-problem
  literature bound such norms from BELOW; upper bounds for sparse R are thin — real research
  risk; the pair family at s = 64, r ≈ 21 is ~2^{40+} — enumeration infeasible without the
  orbit/stratification reduction, and possibly infeasible outright (honest kill condition).
- **Novel**: if it works — the first unconditional prize-parameter (s = 64) ceiling row; if
  it fails — a measured certificate that the TZ external is NECESSARY for s ≥ 64, sharpening
  K4's price tag.
- **Hypothesis**: max over needed pairs of |Res(P−Q, Φ_64)| < 2^{128+80} (so the window
  s = 64, rate 1/4 with p ~ 2^{150} opens unconditionally).
- **Proof plan**: probe: compute exact norm distribution at s = 16, 32 (full enumeration
  feasible) and fit growth; decide feasibility of s = 64 via rotation-orbit reduction +
  norm submultiplicativity pruning; only then attempt certification.

### A4 — The DEEP-quotient transfer engine: list-decoding lower bounds ⇒ MCA lower bounds, generically (B4 converse machinery)
- **Constraints**: issue B4 asks about LD⇒MCA *collapse* (good LD ⇒ good MCA, open); but the
  CONVERSE direction — BAD list decoding ⇒ BAD MCA — is exactly KKH26's Appendix-A item1→item2
  step: from a big list L at u, quotient u₀ = u/(x^m − z^m), u₁ = 1/(x^m − z^m) at a point z
  where many list elements separate, supplied by BCIKS20 Lemma 3
  (E_α|L(α)| ≥ ½·min{|L|, |S|/A} for families pairwise agreeing on ≤ A points).
- **New direction**: formalize the transfer GENERICALLY: any word with list size L at radius
  δ−η over a smooth-domain RS code yields a stack (u₀,u₁) with ≥ L/2 bad scalars at the
  adjusted radius — making every future list-decoding lower bound (including the in-tree
  Johnson-side counts and any A2 improvement) automatically an `epsMCA` lower bound via
  `epsMCA_ge_card_div_of_mcaEvent_set`. The witness sets VARY with γ automatically (each
  bad γ's witness is that list element's agreement set) — the construction lives exactly in
  the loophole `unique_bad_gamma_common_witness` mandates.
- **Why nobody has done it**: KKH26 use it once, inline, for their specific u; the generic
  statement (a functor from LD lower bounds to MCA lower bounds) is not in any paper.
- **Larp-check**: BCIKS20 Lemma 3 is real and self-contained (one expectation/double count);
  the quotient trick needs the domain-smoothness (x^m − z^m vanishing structure) — must
  verify the division stays inside the in-tree `evalCode` degree budget; risk: the "z
  separates the list" step needs |F| ≥ poly(n)·L — track the field condition honestly.
- **Novel**: the generic transfer theorem + its wiring into the ledger; turns the two prize
  challenges' coupling (CS25/BCHKS25 prove LD⇒CA upper; this is the lower mirror) into
  in-tree machinery.
- **Hypothesis**: `mca_lower_of_list_lower : ∀ (list-decoding configuration L at radius θ
  with pairwise agreements ≤ A), ∃ stack (u₀,u₁), ∃ G : Finset F, |G| ≥ min(|L|, n/A)/2 ∧
  ∀ γ ∈ G, mcaEvent C θ' u₀ u₁ γ` with θ' the quotient-adjusted radius, for `evalCode` on
  smooth domains.
- **Proof plan**: probe the construction at toy scale (the probe machinery already computes
  exact bad-γ counts — feed it the quotient stacks); formalize Lemma 3 (pure double
  counting); the quotient-degree bookkeeping; compose with
  `epsMCA_ge_card_div_of_mcaEvent_set`.

### A5 — Affine-orbit exactness: quotient the ε_mca computation by the domain's affine symmetry
- **Constraints**: exact ε_mca is computed in-tree probes up to n = 6 (syndrome reduction:
  p^{2(n−k)} pairs); n = 12 needed sampling; the issue comments name "orbit reduction (mod
  the affine group of the domain)" as the next rung; the smooth domain μ_n has affine
  symmetries x ↦ ax (a ∈ μ_n) plus field automorphisms; mcaEvent is equivariant under
  simultaneous domain-rotation + witness-set rotation, and under (u₀,u₁) ↦ (cu₀, cu₁),
  (u₀ + w, u₁) for codewords w (syndrome reduction already exploits the latter).
- **New direction**: prove the equivariance ONCE (in Lean, for `evalCode`: rotation x ↦ gx
  permutes the code — monomial map on coefficients), derive that the sup in `epsMCA` is
  attained on syndrome-orbit representatives, and ship the quotient as both (a) a probe
  speedup of factor ~n·(p−1) (n = 12, p = 61 exact becomes feasible) and (b) a Lean
  `decide`-friendly finite reformulation for machine-checked toy brackets
  (`mcaDeltaStar` of RS[F₅,4,2] at ε* = 2/5 PINNED EXACTLY in Lean — the first exact δ*
  theorem for ANY code, toy or not).
- **Why nobody has done it**: papers don't compute exact ε_mca at all (they bound it);
  the probes did, but the orbit theory was never written down; a machine-checked EXACT δ*
  point would be a first anywhere.
- **Larp-check**: group-action sup-reduction is standard math; the novelty claim is the
  formal equivariance for mcaEvent + the exact toy pin — verified absent from tree (grep)
  and obviously absent from literature (nobody formalizes ε_mca).
- **Novel**: first exact machine-checked δ* value (toy scale); the equivariance lemmas are
  reusable by every future probe and by A2's orbit needs.
- **Hypothesis**: `mcaEvent_rotate : mcaEvent C δ u₀ u₁ γ ↔ mcaEvent C δ (rot u₀) (rot u₁) γ`
  (rot = domain rotation) and `epsMCA_eq_sup_orbitReps`; corollary: an exact `decide`d
  `mcaDeltaStar (evalCode g 4 1) (2/5) = 3/4`-style theorem at RS[F₅,4,2] (exact value from
  the probe table first).
- **Proof plan**: probe upgrade (orbit reduction in the script, n = 12 exact run validating
  the sampled rungs); Lean equivariance (the rotation is `Equiv.Perm` on `Fin n` +
  code-stability lemma); the finite sup as `Finset.sup` over representatives; `decide` or
  explicit case analysis at p = 5.

## Wave-2 status — 2026-06-10/11 (take-over verification pass)

All four wave-2 lanes LANDED (committed in `2dc721701`, imports registered); independent
re-verification of the compile/axiom state in progress (targeted `lake build` of the edited
chain takes hours under fleet CPU contention; per-file `lake env lean` re-checks follow).
Per-lane outcome:

- **A2 LANDED — `KKH26StratifiedSpread.lean`**: `sVal_inj_cross_strata` (cross-stratum
  injectivity at the SAME threshold `p > s^{s/2}`, ℓ¹ budget `r₁+r₂ ≤ s` — the one new
  resultant step), `exists_realizing_subset` (stratum realization via fresh antipodal
  classes; feasibility `(r−2j)+j ≤ s/2`), headline `kkh26_stratified_count`
  (`∑_{j feasible} 2^{r−2j}·C(s/2, r−2j) ≤ #r-sums`, no `r ≤ s/2` restriction), and the
  upgraded consumers `kkh26_stratified_epsMCA_lower_bound` /
  `kkh26_stratified_mcaDeltaStar_le` with radius relaxed to `r ≤ 2^μ` — the bracket now
  reaches BELOW δ = 1/2. Probe anchors (41 at (8,4); 25 at (8,6)) kernel-checked by `decide`.
- **A4 LANDED — `DeepQuotientTransfer.lean`** (+ `QuotientDeepCore.lean`): `deepU0/deepU1`,
  `deep_quotient_line_codeword` (divided-difference quotient step),
  `deepU1_not_extendable` (joint-pair refusal above the budget `|S| ≥ D·m+1` — the
  load-bearing clause the probe's boundary diagnostic identified),
  `deep_quotient_mcaEvent`, headline `deep_quotient_epsMCA_lower_bound`
  (distinct `ĉ(w)` values ⟹ `ε_mca ≥ L/p`). The BCIKS20 Lemma-3 separation supply stays a
  hypothesis (honest; the KKH26 instantiation supplies it explicitly).
- **K5 LANDED — `CurveDecodability.lean`**: `CurveDecodable` ([GG25] Def 3.1, first
  formalization) + `MarkedCurveDecodable` ([Jo26] Def 5.1), `curveDecodable_of_marked`
  (easy half), `relHammingDist_rowComb_le` (Lemma 5.6), **`markedCurveDecodable_interleaved`
  / `curveDecodable_interleaved` ([Jo26] Thm 5.7, unconditional)** reusing the wave-1
  covering lemma; `markedCurveDecodable_of_interpolation` (Lemma 5.2);
  original⟹marked ([Jo26] Thm 5.5) conditional on the named `FarWordSupply` predicate
  (Lemma 5.4's counting input) with `farWordSupply_of_far_pair` as a sufficient condition.
  B2's "needs GG25 Def 3.1 from scratch" is now unblocked: any future GG25-style result
  imports the definition and inherits interleaving stability.
- **TZ wiring LANDED — `KKH26SumsOfRootsOfUnity.lean` (+227 lines, additive),
  `KKH26WitnessSpread.lean` (+173, additive), `KKH26PolyFieldCeiling.lean` (new)**: the
  divisibility route (`collisionResultant`, `kkh26_lemma1_of_not_dvd`,
  `kkh26_mcaDeltaStar_le_of_not_dvd`) and the composition
  `kkh26_mcaDeltaStar_le_of_TZ` — the [KKH26] δ* ceiling at polynomial field size
  `p = Θ(n^β)`, conditional on exactly the named `TZPrimeSupply` ([TZ24] Cor 3.1).
  B3 is complete: explicit-threshold route unconditional, polynomial-field route priced
  at one named analytic external.

**Issue #334 B-residual scoreboard after wave 2:** B1 done (wave 1) · B2 opener done (K5;
the [Jo26] curve-decodability half is formalized, the [GG25] *theorems* remain external
predicates by design) · B3 done (K3+K4+TZ wiring) · B4 still blocked on literature (the
LD⇒MCA collapse direction; the converse engine is A4, in-tree). A-side (the δ* breakthrough)
remains blocked on literature by construction — the bracket substrate is strictly stronger
now (stratified ceiling + polynomial-field conditional + transfer engine).

## Unification observations
1. **The covering lemma is the load-bearing wall of the whole Jo26 layer**:
   `exists_nonzero_notMem_of_proper_family` (in-tree) IS Lemma 3.2, drives K1 (exactness),
   K5 (Thm 5.7 transfer), and A1 (its breaking point at q+1 is exactly where the dichotomy
   lives). One lemma, three consumers — keep it the single source.
2. **KKH26 and the #232 de Bruijn lane are the same mathematics**: bad scalars = sums of
   roots of unity in F_p; distinctness = NON-vanishing (resultant); the #232 machinery
   classifies vanishing. A2 is the bridge; if it lands, `kkh26_lemma1` and the de Bruijn
   assembly should share a common "sum-polynomial" API.
3. **`EpsMCAInterleavedList` (LD⇒MCA upper) and A4 (LD-failure⇒MCA-failure) are the two
   halves of one dictionary**; together they say ε_mca ≈ (interleaved list size)/q up to
   explicit factors — B4's "collapse" question is precisely whether the upper half can be
   made good beyond Johnson. State them adjacently.
4. **Every B-residual consumer is conditional-hypothesis-shaped** (Hab25Johnson pattern):
   TZ (K4), the GG25 curve-decodability input (K5), any future δ* paper (A-side) — the
   named-structure discipline is the unifying architecture; no axioms.

## Closeout audit snapshot — 2026-06-11

Status after the wave-1 formalization (`1d790913b`):

- **B1 is formalized.** `Jo26GeneratorMCA.lean` gives the general-generator `epsMCAGen`
  interface and [Jo26] Thm 4.2/4.4 style factor/equality statements; `Jo26PowerGeneratorInterleaving.lean`
  connects the power-generator surface back to `epsMCAP`.
- **B3 is formalized up to the intended named external.** `KKH26EntropyForm.lean` supplies
  the finite method-of-types/entropy form. `KKH26ThornerZaman.lean` supplies the elementary
  good-prime counting theorem from a `TZPrimeSupply`; the analytic Thorner--Zaman prime-supply
  theorem remains an honest external input, not an in-tree theorem.
- **The KKH26 Lemma-1 plumbing exists in-tree.** `KKH26SumsOfRootsOfUnity.lean` now has both
  the old explicit-threshold route and the issue-#334 divisibility route
  (`collisionResultant`, `not_isRoot_of_not_dvd_resultant`, `sVal_injOn_of_not_dvd`,
  `kkh26_lemma1_of_not_dvd`). Future audits should treat the Thorner--Zaman bridge as wired
  into the in-tree divisibility API.
- **Two "residual-looking" predicates in the proximity scan are already discharged.**
  `PrefactorWeightMatch` is proved by `prefactorWeightMatch_holds`; `GK16Lemma12HardResidual`
  is proved by `gk16Lemma12HardResidual_holds`. They may still intentionally exist as named
  hinge predicates, but they are not open mathematical debt.
- **The remaining `CapacityBoundsProofs.lean` residuals are paper-level external interfaces.**
  The GKL24, BGKS20, BCHKS25/KK25, CS25, and GG25 predicates package external theorems so
  downstream results stay conditional rather than smuggling in axioms. Discharging them would
  mean separately porting those papers' full proofs, not just rephrasing the declarations.
- **The MCA-conjecture refutation remains conditional.** `CS25BreakdownLowerResidualUniversal`
  is the CS25 Corollary-1 lower-bound external, and `CS25BandInstanceBelowConjectureBound` is
  the remaining arithmetic/regime witness. The in-tree theorem honestly proves that these two
  inputs imply `¬ mcaConjecture`; it does not prove the unconditional refutation by itself.

Additional web/literature sweep on 2026-06-11 found adjacent progress but no δ* breakthrough for
explicit smooth-domain Reed--Solomon MCA:

- Folded Reed--Solomon/subspace-design papers reach capacity for related folded/subspace-design
  code families, not the fixed smooth-domain RS family targeted by the prize δ* question.
- Syndrome-space/random-linear-code approaches give direct proximity-gap machinery for random
  linear codes, again not the explicit smooth-domain RS bridge from Johnson to capacity.
- The public Proximity Prize statement still asks for the largest δ* for smooth-domain RS at
  fixed rates and ε*; the gap between `1 - sqrt ρ` and `1 - ρ - Θρ(1 / log n)` remains the
  honest open interval for this tracker.

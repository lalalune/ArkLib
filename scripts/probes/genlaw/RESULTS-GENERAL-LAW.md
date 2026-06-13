# The general rung law: the antipodal-balance engine at every 2-power scale, with a blind n=64 forecast that survived independent enumeration

Lane `nubs/issue232-effective-pa`, 2026-06-10. Successor tracker: #334 (descent / per-level
law residuals). Predecessors: C19's 19 = 3 + 16 (n=16), O87's ℓ₃₂(w,18) = 35 (n=32 level 1),
O98/O108's 672/1,344 + the derivation engine (n=32 level 2; `../n32census/level2/DERIVED-672.md`).

**Protocol.** Three independent agents, blind to each other's numbers: a *generalizer*
(re-derive C19's 16 at n=16 as a calibration gate, then produce the general-s law and a blind
n=64 forecast), a *verifier* (independent enumeration at n=64 from the raw balance criterion,
different algorithm, plus constructive mod-p checks), and an *adversarial audit* (third
implementation, arbitrates every disagreement). Everything below survived the audit
(confidence 0.92); the one forecast/verifier disagreement was resolved **in the forecast's
favor** by the audit's third count (see §4).

## 1. The setup (all 2-power s)

`s = 2^j` (j ≥ 3), `n = 2s`, `H = μ_n`, `z* = ζ_n^{s/2}`, word `w = X^{s+2} − z*·X^s`,
code = RS degree < s (the per-level descent instance; C19 is `s = 8`, O87/O108 is `s = 16`).
Fibers of `x ↦ x²` pair into `m := s/2` axes; the −z* fiber sits at `3s/4`, the L-axis at
`s/4 (mod m)`.

## 2. The law (what is now derived for every 2-power s)

- **Layer dichotomy (theorem grade).** Agreement > s+2 is impossible. The witness layer
  (agree s+2) has size **exactly `C(s/2 − 1, s/4)`**: even-r patterns die a priori
  (e₁ = 0 would need an antipodal pair across distinct fibers), and the r = 0 balance
  forces fiber s/4 in, fiber 3s/4 out, with s/4 free antipodal pairs on the remaining
  s/2 − 1 axes. Rungs: 3 (s=8), 35 (s=16), 6,435 = C(15,8) (s=32), 300,540,195 = C(31,16)
  (s=64). This is the single highest-confidence statement here — pure balance argument,
  no enumeration.
- **Marginal layer (agree s+1).** Every element has fiber pattern (b, r), 2b + r = s+1,
  r odd; for **every** odd r ≥ 3 the same 3-line symmetric-function identity reduces the
  consistency equation to **antipodal balance** of the multiset
  `{xᵢxⱼ}_{i<j} ⊎ O_z ⊎ B_z ⊎ {−z*}`, and L4 (ξ = −Σxᵢ ∉ μ_n ∪ {0}) holds for all odd r,
  so balanced configs are *exactly* the marginal layer, with free negation. Hence
  `marginal(s) = 2·Σ_{r odd ≥ 3} N_r(s)`.
- **N₃ closed structure (general).** Parity-purity (L1), the complete E1–E4 event taxonomy
  (mod-2^t arguments), and the **universal node geometry** — 13 node types with invariant
  (h, v−m, σ) data, machine-asserted identical at s = 8, 16, 32; always k = (m−1−h)/2,
  σ = 4/2^{#independent P-side constraints}. Census closed forms verified at m = 4, 8, 16:
  E1 = E2 = E3 = (m/2)(m−2) per ε (E1 proven), pairwise = m, ε₀ dead = (m−2)²/2, etc.
- **Calibration (the gate).** The engine at s = 8 reproduces C19's 16 with **no fix**
  (8 classes × free negation; exact (B,O,σ) set equality against a fresh full C(16,9)
  interpolation census at BabyBear). What calibration killed: the "perfect 7×8 split" and
  "pairwise = m" patterns are m = 8 coincidences, not law.

## 3. The blind n=64 forecast vs. independent truth

| quantity | generalizer (blind) | verifier (independent) | audit (3rd impl.) |
|---|---|---|---|
| witness ℓ(w, 34) | 6,435 = C(15,8) | 6,435 (same balance law) | re-derived by hand |
| r=3 stratum classes | 764,544 | **764,544** (exact element-set equality) | **764,544** |
| r=3 elements | 1,529,088 | 1,529,088 | 1,529,088 |
| r=5 stratum classes | 99,512 | *(not swept — see §4)* | **99,512** |
| marginal total | **1,728,112** = 2·(764,544 + 99,512) | — | confirmed for r ≤ 11 |

The r=3 agreement is three fully independent implementations (forced/free-axis engine;
direct enumeration from the raw criterion calibrated on the proven s=16 truth; the audit's
per-axis generating-polynomial DP sweeper), agreeing **to exact set equality** of all
764,544 solutions. Strata, ε-split (373,440/391,104), B-census (703,656 distinct B =
642,768 ×2 + 60,888 ×4 — the {2,4} menu's third rung), dual-B split (14,520 share-2 +
46,368 disjoint), parity-purity, and σ-uniqueness all match across implementations.

Field checks: 300 stratified constructive codewords at BabyBear (agree exactly 33;
predicted zero-set matched exactly; 50/50 negative controls fail) + 24+24 audit samples at
BabyBear and p₂ = 3·2³⁰+1; witness samples agree exactly 34.

## 4. The discovery: higher-r strata turn on with s

**"Marginal = the (s/2−1, 3) family" is an s ≤ 16 smallness fact, not a law.**
N₅(8) = N₅(16) = 0, but **N₅(32) = 99,512** (pattern (14,5)) — 16 non-B terms fit on 16
axes at s = 32 but not on 8 axes at s = 16. The verifier's initial 1,529,088 "total" was
the incomplete number (r=3 only); the audit's independent sweep + 30/30 assumption-free
raw-brute spot checks (full C(27,14) ≈ 2.0×10⁷ B-subsets per class) + 24 field samples
confirmed the r=5 stratum is real. It has its own structure: all-B-multiplicity-1 (menu
degenerates to {2}), mask-uniqueness, five **new z\*-axis slot types**, a new event E5
(antipodal product–product pairs, census {0: 3,768, 1: 7,880, 2: 160}), and **L3 breaks**
(2,784 classes put a product on the −z* fiber: LP|OP 288 + BP|LP 2,496).

Exclusion sweeps (exhaustive, C kernels, independently replicated at r ≤ 9):
N₇(32) = N₉(32) = N₁₁(32) = 0 (r=11: 1.32×10¹¹ sign-configs, 8-way; all workers 0;
audit validated the kernel logic exactly at r = 3, 5 but its own r=11 replication did not
finish — residual risk explicitly noted). s=16 re-swept independently to r = 15: all 0
(DERIVED-672's completeness independently re-established).

**Level-4 anchors (s = 64, n = 128)**, computed with the audit's corrected sweeper:
N₃(64) = 244,593,584,640 (34,280 classes); N₅(64) = 141,450,979,280 (2,212,000 classes);
**N₇(64) = 1,586,840,480 (3,300,096 classes)** — measured 2026-06-10 (4-way sweep,
~4×10¹⁰ configs; kernel calibrated on 99,512 / 0 / 672 and the 4-way split validated to
sum exactly 99,512 on s=32 r=5; raw logs `s64r7_sweep.txt`). **The turn-on staircase is
now structural** (`exclusion/REPORT.md`, audited): **T1 [PROVEN, all scales]** — parity
purity for every odd r ⟹ N_r(s) = 0 unconditionally for r > s/2 (the whole deep tail);
**T3 [PROVEN]** — doubling monotonicity (N_r(s) ≥ 1 ⟹ N_r(2s) ≥ 1): strata never turn
back off. The boundary is conjecturally the **sharp law N_r(s) > 0 ⟺ r² ≤ s+1**
(26/26 calibration; explains the s=8 tightness 9 ≤ 9). The earlier r_max = 2j−5 guess is
**REFUTED** by 29 doubly-verified explicit certificates: N₁₁(128) > 0, N₁₃(256) > 0,
N₁₅(256) > 0, N₁₇(512), N₁₉(512) all > 0. Named open boundary points: (64, 9) — the
sharp law predicts 0, enumeration did not finish; (512, 21) — law predicts ON, no
certificate found (climbs stall); the middle band √(s+1) < r ≤ s/2 has no structural
proof above s = 32. marginal(64) ≥ 2·387,631,404,400 = 775,262,808,800 remains a lower
bound pending the (64, 9..31) band.

## 5. Honest caveats (what would move the numbers)

1. ~~The r ≥ 13 tail at s = 32 is unswept~~ **CLOSED (2026-06-12, `exclusion/REPORT.md`
   T4): marginal(32) = 2·(N₃+N₅) = 1,728,112 is COMPLETE.** N_r(32) = 0 for ALL odd
   r ≥ 7: r=7 by full 215,414,784-config sweep; r = 7..15 by pure-only exhaustive
   enumeration (legitimate by the proven parity-purity theorem T1); r ≥ 17 by T1's
   corollary outright (r > s/2). The same method independently re-establishes
   DERIVED-672 completeness at s=16 (third implementation). A raw (mixed-parity
   included) r=13 sign-config sweep ran as belt-and-suspenders until T4 landed: 5 of 8
   workers (62.5% of the O-space) returned raw 0, fully consistent; terminated as
   redundant once the proof + pure-only enumeration closed the question.
2. **All counts are char-0** (ℤ[ζ_n]) statements — and the per-prime falsifier (run
   2026-06-11, `falsifier/`) **measured the transfer FAILING at n=64**: the consistency
   equation is linear in the B-subset sum, so an exhaustive per-class meet-in-the-middle
   scan of ALL pattern-(15,3) classes is feasible, and it found **+11 spurious mod-p
   solutions at BabyBear (764,555 vs 764,544; 2 classes) and +54 at p₂ = 3·2³⁰+1
   (764,598; 10 classes)** — every spurious config triple-checked as a genuine
   agree-exactly-33 marginal codeword that is NOT char-0 balanced (p divides the norm of
   a bad lattice vector α with L1 norm 14–18). Calibration: n=32 gives exactly 672 = 672
   at both primes (zero spurious, matching the exhaustive O98 census); small-prime
   controls (p=97 at n=32, p=193 at n=64) show massive spuriousness at the uniform
   heuristic, as expected. So the n=64 forecast numbers are exact in char-0 and **per-prime
   lower bounds with a measured tiny surplus** at the production primes; the surplus is
   prime-specific, not structural. **The r=5 scan (complete, both primes) shows the
   surplus scales with pattern complexity: BabyBear 132,965 = 99,512 + 33,453 (33.6%
   relative), p₂ 116,453 = +16,941 (17.0%)** — at (14,5) the α-lattice is rich enough
   that p | N(α) is generic at ~2³¹ primes; the char-0 core carries a large generic
   mod-p halo (all of it on char-0-infeasible classes at BabyBear; at p₂ exactly one
   feasible class inflates by 1). 50/50 brute==MITM samples; 447 spurious configs
   reconstructed end-to-end (`falsifier/`). The witness-layer surplus question and odd
   r ≥ 7 remain unscanned mod p (r = 1 is excluded mod p by the same prime-independent
   ξ ∈ μ₆₄ argument as char-0).
3. Census closed forms beyond the verified families are fits (m = 4, 8, 16), not proofs;
   ε₀ censuses are irregular through m = 4 — use the O(m³) per-s enumeration.
4. The r=5 taxonomy (E5 + placement) is **charted, not derived**; taxonomy completeness for
   r ≥ 5 is open. At s = 64 expect N₇ as the next turn-on candidate.
5. z*-axis strata are reported in two naming dialects (generalizer vs. verifier); the audit
   reconciled them numerically (s=16: 224/96/160/192 ⇔ 224/96/304+48). Future docs should
   fix one dialect.
6. **Porting warning:** extending the `sweep32*.c` kernels to s = 64 hits a 32-bit O-fiber
   bitmask UB for fibers ≥ 32; `audit/audit_sweep64.c` is the corrected version (revalidated
   against an independent Python reimplementation on 34,280 records + 4,000 random configs).

## 6. Lean status

The engine's foundational criterion (2-power vanishing sums ⟺ antipodal balance, with
multiplicities/coefficients) is **already in-tree**, landed independently by the swarm during
the same hours: `LamLeungTwoPow.vanishing_iff_antipodal_coeffs` (ℚ-coefficient iff — strictly
stronger than the ℤ form) and `LamLeungMultisetAntipodal.multiset_antipodal_iff` (element-level
multiset form). The brick written for this run (`audit/redundant_MultisetLamLeung.lean.txt`,
compiles clean, axiom-clean `[propext, Classical.choice, Quot.sound]`, audited) is therefore
**redundant and intentionally not landed** — kept here as the independent confirmation it
turned out to be.

## 7. Artifact inventory

Generalizer: `engine.py` (forced/free-axis engine, all s), `n16_groundtruth.py` (fresh C19
census), `census_forms.py`, `pattern_sweep.py`, `sweep32.c`/`sweep32p.c` (exclusion kernels),
`anatomy_r5.py`, `verify_field64.py`, `FORECAST_n64.json` (the blind forecast, timestamped
before the verifier returned), `s32_run.txt`, `sweep_logs.txt` (r=11 8-way + r=5/r=9 logs).
Verifier: `verify_n16.py`, `enumerate_n64.py`, `construct_n64.py`, `raw_brute.c`,
`run_raw_brute.py`. Audit: `audit/` (third-implementation sweepers incl. the corrected
s=64 kernel, raw-brute checker, field census, n=16 triple-check). The 61 MB
`n64_sols.json` (all 764,544 r=3 solutions) is regenerable via `enumerate_n64.py` and not
committed.

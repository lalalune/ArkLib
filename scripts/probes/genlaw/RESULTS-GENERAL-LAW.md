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
sum exactly 99,512 on s=32 r=5; raw logs `s64r7_sweep.txt`). **The turn-on is now a
recurring phenomenon, not a one-off:** active strata {3} at s=8,16 → {3,5} at s=32 →
{3,5,7} at s=64 (consistent with r_max = 2j−5 for s = 2^j, j ≥ 4 — pattern-extrapolated,
NOT derived; predicts r_max = 9 at s=128). So marginal(64) ≥ 2·387,631,404,400 =
775,262,808,800 — still a **lower bound only**: the r ≥ 9 tail at s = 64 is unswept
(~7.05×10¹² configs at r=9, r=13@s=32-scale compute).

## 5. Honest caveats (what would move the numbers)

1. **The r ≥ 13 tail at s = 32 is unswept** (C(32,r)·2^{r−1} ≥ 1.4×10¹²). The 1,728,112
   total is proven only for r ≤ 11; the r=5 turn-on proves strata do switch on, so
   "predicted 0" is genuine extrapolation. r=13 (~18 core-h) is feasible and recommended;
   closing the tail for good needs a structural exclusion theorem, not sweeps.
2. **All counts are char-0** (ℤ[ζ_n]) statements. BabyBear sits below the effective-transfer
   norm threshold at these m, so mod-p agreement rests on spot checks (45+ samples, 2 primes,
   all passing), not on the E1 norm bound. The n=32-style exhaustive per-prime census is
   infeasible at n=64 (C(64,33) ≈ 7×10¹⁷); the feasible falsifier is enumerating the 864,056
   char-0 configs mod p with the norm-divisibility criterion.
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

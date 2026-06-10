# The n=32 mixed-branch census: ℓ₃₂(w, 18) = 35 — the structured core EXACTLY exhausts the beyond-Johnson list

Lane `nubs/issue232-effective-pa`, 2026-06-10. The decisive computation named by the descent
program (07-DESCENT/O13″ "the decisive single computation"; claimed in #232 comment 4666108014),
executed in O63's coefficient-slice frame with a hard calibration gate and a fully independent
adversarial re-sweep.

## Setup (deterministic, no seeds)

p = 15·2²⁷+1 (BabyBear); generator g₀ = 31 (smallest primitive root — the proximity-research
probe convention); H = μ₃₂, G = μ₁₆ enumerated by g₀-powers; code RS[F_p, H, 16] (ρ = 1/2);
line X¹⁸ + λX¹⁶ with λ = (−e₁*) mod p = 284861408, e₁* = g₀^((p−1)/4) — the max-fiber
(C(7,4) = 35) e₁-value on 9-subsets of G under the KB tie-break. The max-fiber tie class is
EXACTLY the μ₁₆-orbit of e₁* (16 values, incl. e₁ = 1); the substitution x ↦ ux (u ∈ μ₃₂)
maps tie words isomorphically onto each other, so the census count is tie-independent
(rigorous orbit argument, audit-strengthened; also measured end-to-end at a second tie value:
identical 35). Threshold a = 18 = the witness agreement level (radius 14/32 = 0.4375,
beyond Johnson ≈ 0.2929; η = 1/16).

## Method

Finite-difference functional sweep over ALL C(32,17) = 565,722,720 subsets (exhaustive: every
list element has agreement ≥ 18 ≥ k+1 = 17, so every 17-subset of its agreement set passes the
functional and determines it by interpolation; the functional is a scalar — no degenerate
branch). C kernel (`census_kernel.c`, gcc -O3): precomputed 32×32 inverse-difference table,
272 mulmods/subset, ~0.81 µs/subset; 16 chunks by smallest element, per-chunk swept-counts
equal C(31−i₀,16) exactly (coverage cross-foot = C(32,17)); 244 s wall on 8 cores.

**Calibration gate (passed before n=32 was believed):** the same code path at n=16
(C(16,9) = 11,440) reproduces the C19 ground truth bit-exactly: list = 19 = 3 witnesses
(agree 10, all-even support) + 16 dense (agree 9, full support), with the cross-foot
46 = 3·C(10,9) + 16·C(9,9) passes.

## Results

- **ℓ₃₂(w, 18) = 35, exactly.** 1,974 functional passes → 630 emissions = 35·C(18,17)
  (cross-foot exact) → 35 distinct codewords, every one independently re-verified.
- **All 35 are the structured witnesses** u_S(X²) over the 35 fiber subsets S — the census
  equals the constructed family 35/35. **Zero dense enrichment at the witness level**:
  Entry-11's n=16 finding holds at n=32 scale. Agreement histogram {18: 35}. Enrichment
  ratio 1.000.
- **The agree-exactly-17 layer (one notch below): exactly 1,344** (derived rigorously from
  pass accounting, then enumerated DIRECTLY by the audit's independent kernel: 1,344 distinct,
  each from exactly one subset, disjoint from the 35, all full-coefficient-support — the
  0 all-even count is forced by parity symmetry). So ℓ₃₂(w, 17) = 1,379. Notch-enrichment
  1379/35 ≈ 39.4 vs n=16's 19/3 ≈ 6.33 — polynomial-consistent growth (H3′), far below
  every budget line.
- **O63 coefficient-spread stratification** (digit code verified against the slice
  definitions and a numeric fold tree; the naive binary code provably fails — the twist
  shift is real): all 35 are depth-1 class (0); at depth 3, 32 elements occupy 4 mod-8
  classes and 3 occupy 2 — the first 2-adic spread chart of a real beyond-Johnson list.
- **Thresholds:** 35 < 3,280 = N₀(16,9) ≪ 32·3280 = 104,960 (Conjecture-D falsification
  line — **D is not falsified; it is maximally confirmed at this word and radius**);
  35/65,536 ≈ 0.05% of the c=1 budget 2^{H₂(1/2)/η} = 2¹⁶.

## Verification trail

Adversarial audit (sound, 0.97): full independent re-sweep with a from-scratch C kernel
(Newton divided differences over all 17 points — a different algorithm), all elements
re-verified end-to-end, both λ-words run completely, coverage hashes reproduced, modular
arithmetic audited, n=16 calibration reproduced two independent ways, blind spots
(agree-17 exclusion, degenerate functional, duplicates) all checked.

Reproduce: `gcc -O3 -march=native census_kernel.c -o census32 && for i in $(seq 0 15); do
./census32 $i out_$i.txt & done; wait; python3 postpass.py` (~4 min on 8 cores).

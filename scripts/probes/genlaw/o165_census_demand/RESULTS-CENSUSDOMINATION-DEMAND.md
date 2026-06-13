# Falsify-first on the $1M Prop: CensusDomination's demand side HOLDS WITH MARGIN at n=16

2026-06-13. Goal: compute the EXACT deep-band bad count vs the budget `K = 2^r·C(n/2,r)`
where the packing route provably fails, and decide whether CensusDomination actually holds.
Opus 4.8, three legs (pin → compute → adversarial verify), all faithful-prime exact, triple
independently reproduced. **Decisive at the computable frontier (n=16); n=32 worst-case is
infeasible.**

## The result (two parts, both honest)

**1. The δ\*-gating quantity HOLDS WITH MARGIN.** The quantity CensusDomination actually
needs bounded — the worst-case-over-stacks deep-band **#bad-scalar** count — stays well under
the KKH26 budget `K = 2^r·C(8,r)` at every deep band, faithful BabyBear (`p² = 4×10¹⁸ ≫
C(16,8) = 12,870`, so no O164 saturation artifact):

| r (deep band, a₀ = r+1) | worst-case #bad | budget K | margin |
|---|---|---|---|
| 3 | 97 | 448 | 4.6× |
| 4 | 145 | 1120 | 7.7× |
| 5 | 89 | 1792 | 20× |
| 6 | 113 | 1792 | 16× |
| **7** (a₀=8) | **225** | **1024** | **4.6×** |
| **8** (a₀=9) | **104** | **256** | **2.5×** |

Tightest at the deepest prize-critical bands (r=7,8). Every count calibrated `≤` the packing
upper bound `C(16,a₀)/(a₀+1)`. **This is the first direct, faithful, positive evidence the
prize Prop is true at the demand level.** The worst-case stack is a high-frequency monomial
pair (`x⁸ = −1`, the order-2 element), NOT the canonical KKH26 stack — which gives #bad = 0
at the deep band (its supply lives one band shallower, at the ceiling `a = rm`, validated:
ceiling #bad = 113, 464, 1233, 2256, 3025, 3280, 3281).

**2. The LITERAL CensusDomination (alignable-SETS form) is FALSE at the deep band** — a
degenerate codeword stack (`u₀` constant in degree-`<k_c`, `u₁` a codeword) makes `γ = 0`
own all `C(n,a₀)` a-sets (#alignable = 1820/8008/12870 ≫ K, up to 12.6× at r=7) while pinning
exactly **one** bad scalar. This is **not** a δ\* refutation — it is the documented lossy
overcount (`SinglePencilQIndependence.lean` L19-23: the alignable-sets bound "overcounts
massively"). **The correct in-tree obligation is the #bad-SCALAR form**
(`badScalars_card_le_alignable` + the SinglePencilQIndependence route), not the literal
alignable-sets cap. Anyone discharging CensusDomination must target the bad-scalar form.

## Verification (why this is believed)

Triple-independent: the count was reproduced by (a) the builder's Gauss-elim/modular-ratio C
kernel, (b) a Laplace-expansion + closed-form-Vandermonde-minors C kernel, (c) from-scratch
Python Bareiss fraction-free determinant + itertools — **digit-for-digit agreement**. The
tightest counts are **invariant across three distinct faithful primes** (rules out the O164
pigeonhole artifact). Residual definition cross-checked against the Lean ground truth
(`OwnershipBound.residual`, `UniversalAlignmentLaw.Aligned`, `CensusDominationWeld`'s filter).

## Honest scope

- **n=16 is the exact worst-case frontier.** n=32 deep band: one stack-band is C(32,17) ≈
  5.7×10⁸ subsets (~9 min/stack); a worst-case *search* (~30-100 stacks) is days even on a
  C kernel, and the syndrome-reduction route is `q^{2(n-k)}` at a faithful `q ~ 2×10⁹` =
  astronomically infeasible without an (open) rotation-quotient restriction. So n=32 admits
  only single-stack spot-checks, not a verdict.
- This is char-0-faithful demand counting at one rate family (m=1); it does **not** prove
  CensusDomination (that needs all n, the analytic Stepanov/Weil route the swarm is building).
  It is the first *direct evidence* the Prop holds in the form that matters, plus the sharp
  correction that the literal set-form is the wrong obligation.

Complements the other NubsCarson seat's O164 (the fiber/supply side, max fiber = O(1)):
together, #alignable ≈ #bad × fiber, and both factors are now measured small at n=16.

Reproduce: `pin_n16.py`, `cd_demand.c`, `worstcase_badscalar.py`, `crosscheck_r7.py`;
independent re-checks in `o166_verify/` (`indep.c`, `indep2.c`, `brute.py`).

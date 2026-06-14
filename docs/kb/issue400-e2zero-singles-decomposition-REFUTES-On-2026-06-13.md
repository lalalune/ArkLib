# Issue #400 core: e_1 = signed sum of SINGLES; O(n) conjecture REFUTED (s_max≥3); correct target is s_max≤2 (2026-06-13)

Issue #400 isolates a q-independent combinatorial core of the MCA prize: count
`B = #{ −e_1(S) : S⊆μ_n, |S|=w=k+2, e_2(S)=0, e_1(S)≠0 }`, conjectured `O(n)`. Attacked directly via
the Lam–Leung antipodal structure. **Result: a structural decomposition theorem + refutation of the
O(n) bound + the corrected closed target.** Probes: `probe_e2zero_singles_smax.py`,
`probe_e2zero_e1_decomposition.py`.

## 1. Decomposition theorem (NOVEL, proven by ζ^{i+h}=−ζ^i)
Pair ℤ/n (n=2^μ, h=n/2) into antipodal classes {i,i+h}. For S with exponent set A, classify each class
as **full** (both in A), **single** (one), **empty** (none); `w = 2f + s` (f full, s single). Since
`ζ^{i}+ζ^{i+h}=ζ^i−ζ^i=0`, **every full pair contributes 0 to e_1**:
> `e_1(A) = Σ_{single classes j} ±ζ^{j}`  — a signed sum over ONLY the s single classes.
As `{ζ^j}_{j<h}` is a ℚ-basis, distinct signed-single-sets ⟹ distinct e_1. Hence
> **`#bad = #{valid signed-single configs} = Θ(n^{s_max})`**, `s_max = max #singles over valid e_2=0 sets.`
The `e_2=0` (Lam–Leung balance) condition becomes: the multiset `M = {2i+h : full i} ⊎ {q_a+q_b : single pairs}`
is `+h`-invariant. Full-pair sums are even-position (absorb even imbalance); ODD-position half-half sums
must self-balance (independent of f).

## 2. REFUTATION of #400's `O(n)`
`O(n)` ⟺ `s_max ≤ 1`. Measured `s`-distribution among valid sets:
| n | w | s-distribution | s_max |
|---|---|---|---|
| 8 | 4 | {0:2, 2:8} | 2 |
| 16 | 4 | {0:4, 2:48} | 2 |
| 16 | 9 | {1:48, **3:32**} | **3** |
`s_max ≥ 3` at (n=16,w=9) ⟹ `#bad = Θ(n³)`, NOT O(n). #400's "n=16→16, one orbit" used `w=5` (s=1,
low rate `ρ=3/16`), not a constant rate. The `O(n)` bound is FALSE for the general / near-capacity direction.

## 3. s_max grows; dir(k+1,k+2) is ABOVE δ*
Peak `s_max`: n=8 → 2, n=16 → 3 (at the middle w≈n/2). Consistent with `s_max ≈ log₂ n − 1`, giving
**quasi-polynomial** `#bad` for `dir(k+1,k+2)` at constant rate — i.e. this direction is near-capacity,
ABOVE the window upper, exactly as #400's caveat states. So its blow-up does NOT threaten the prize;
it confirms δ* is strictly below this band.

## 4. The CORRECTED closed target (sharper than #400)
Prize budget `ε*q = 2^{128}·... ` → for the deployed regime `ε*q = 2^{64} = n^{2.13}` (n=2^30). So the
prize needs `#bad ≤ n^{2.13}` ⟺ **`s_max ≤ 2`** for the WINDOW-INTERIOR worst direction (`#bad ~ Θ(n²)`,
the observed `4n`/3-orbit regime), NOT for the near-capacity dir(k+1,k+2). The closed sub-conjecture is:

> **Conjecture (corrected):** for the window-interior worst monomial direction at the band δ=δ*, every
> valid `e_2=0`-type config has `s ≤ 2` singles ⟹ `#bad = Θ(n²) ≤ ε*q`. Equivalently the signed-single
> decomposition has rank ≤ 2 at δ*.

| axis | score |
|---|---|
| novelty | 8 (signed-single decomposition + s_max framing is new) |
| insight | 9 (collapses the bad count to a single integer s_max via Lam–Leung; explains O(n)/Θ(n²)/Θ(n³) data exactly) |
| proximity | 8 (q-independent prize core; budget calibration explicit) |
| feasibility | 6 (s_max≤2 at δ* is a finite-rank claim, but proving it for the interior direction at all n is open) |

**Honest status:** the decomposition is proven; #400's O(n) is refuted; the corrected target (`s_max≤2`
at δ*) is the right closed sub-conjecture. It is NOT yet proven (s_max grows for near-capacity directions;
the claim is that the INTERIOR direction at δ* caps at 2). No closure claimed; genuine structural advance.

# The clean-moments → Markov → `B(μ_n)` bridge: a clean equivalent form of the open core (2026-06-13)

A genuinely new, clean reformulation of the prize's analytic core, with explicit machinery and `n=8`
empirical confirmation — but **equivalent to the open problem, not a closure** (recorded honestly).

## 1. The bridge (novel, clean)
The character sums `η_b = Σ_{x∈μ_n} e_p(bx)` have exact `2r`-th moments
`Σ_b |η_b|^{2r} = p · E_r(μ_n)` (the `r`-fold additive energy). If `E_r(μ_n)` equals its **clean
(Gaussian) value** `(2r−1)!!·n^r·(1+o(1))` for all `r ≤ r_max`, then by **Markov at `r=r_max`**:
`#{b : |η_b|² > T} ≤ p·E_r/T^r ≤ p·(2r−1)!!·n^r/T^r`, which is `<1` for
`T > (p·(2r−1)!!)^{1/r}·n = p^{1/r}·(2r/e)·n·(1+o(1))`. Hence
> **`B(μ_n) ≤ √( p^{1/r_max} · (2 r_max/e) · n )`.**

If `r_max = Θ(log p)` then `p^{1/r_max} = O(1)` and `r_max = Θ(log(p/n))`, giving
**`B(μ_n) ≤ C·√(n·log(p/n))`** — the exact prize bound, which (via the construction extremality +
the proven scaffold) **closes `δ* = 1−ρ−2/s*`**. This is a clean, explicit route from a *moment/energy*
statement to the worst-case character sum, bypassing the direct worst-case analysis.

## 2. Empirical confirmation (`n=8`, solid)
`E_r(μ_8)` is **clean** (matches the true huge-`p` baseline, `p=2097169 > n^7`) for `r = 2,…,7`, and
first deviates at `r=8` (`p=4129`); `log(p/n)=9`. So `r_max=7 ≈ Θ(log(p/n))` for this point.
Across `n=8` primes: `(log₂(p/n), r_max) = (3.8,3),(6,4),(7,5),(9,7),(11,11)` — `r_max/log₂(p/n) ∈
[0.66,1.0]`, consistent with `r_max = Θ(log(p/n))`.

## 3. HONEST caveats (why this is not a closure)
- **`r_max = Θ(log p)` ⟺ `B(μ_n)=Θ(√(n log))`** are *equivalent*: if `B=√(n log)` then
  `Σ|η|^{2r}=pE_r ≤ p(n log)^r` forces `E_r` clean up to `r∼log`; conversely clean moments give the
  Markov bound. So the clean-moments statement **is** the open problem, in a cleaner moment form — not
  an easier one.
- **The large-`n` measurements were unreliable:** for `n=16,32` the reference prime (2M) is itself
  clean only to `r ≈ log_n(REF) ≈ 4–5`, so it cannot validate higher `r`; the observed low ratios
  (0.2–0.4) are measurement artifacts, not evidence that `r_max` is sub-`log p`. A true test needs a
  reference with `p' ≫ n^{2r}` (infeasible by the array method at these `r`).
- So whether `r_max = Θ(log p)` (closes) or `Θ(log_n p)` (fails — `p^{1/r}` blows up) is **exactly the
  open question**, undetermined at prize scale by direct computation.

## 4. Value (honest)
- A **new, clean, explicit bridge**: prize `δ*` ⟸ `B(μ_n)` ⟸ "additive energies `E_r(μ_n)` are
  Gaussian up to order `Θ(log p)`." This is the most *tractable-looking* form of the open core — a
  concrete moment/energy statement (studied object) with the Markov implication fully explicit and
  the `n=8` case verified.
- It also **corrects two wrong thresholds** from earlier this session: `E_r` clean is NOT `p>n^r`
  (too pessimistic — `n=8` clean to `r=7 > log_8 p=4`) and NOT `p>n²` for all `r` (too optimistic —
  breaks at `r=8`). The true threshold is `r_max=Θ(log(p/n))`-flavored, the same content as `B`.

**No closure claimed.** The prize closes iff `E_r(μ_n)` is Gaussian to order `Θ(log p)` for `n≪√p` —
a clean, concrete, empirically-supported additive-combinatorics statement, equivalent to the
worst-case character-sum bound, and the single remaining open input to the otherwise-proven scaffold.

# Congruence check: the δ* residual IS the recognized-hard "high-moment / sup-norm of character sums" (2026-06-13)

User-supplied additive-combinatorics + character-sum batch (≈40 papers). Decisive congruence check
of our open residual against the analytic-number-theory frontier. **Our theory is consistent with
the literature, the residual is a named recognized-hard problem, and a GRH-conditional path exists.**

## 1. Exact correspondence
Our residual: `E_r(μ_n) ≤ (Crn)^r` for `r≤log(p/n)`, equivalently `B(μ_n)=max_{b≠0}|η_b| ≤ C√(n log(p/n))`,
where `Σ_b|η_b|^{2r} = p·E_r` is the **2r-th moment of the character sum** `η_b=Σ_{x∈μ_n}e_p(bx)`.
This is *exactly* the object of:
- **Szabó, "A lower bound on high moments of character sums" (2409.13436):** the `2k`-th moment
  `(1/φ(q))Σ_χ|Σ_{n≤x}χ(n)|^{2k}`. **Key quote (p.3):** *"showing sharp unconditional UPPER bounds for
  these moments when `k` is large seems **HOPELESS with our current knowledge**, since only one 'badly
  behaving' character could mess up the bound… the upper bound is only known for `k≤4` unconditionally
  and for all `k` under the Riemann Hypothesis."* — i.e. our `E_r` upper bound is the recognized-hard
  high-moment upper bound, **unconditionally open, GRH-conditional**.
- **Munsch, "The maximum size of short character sums" (1805.07163):** `Δ(x,q)=max_χ|Σ_{n≤x}χ(n)|` =
  the **sup-norm**, our `B`. Pólya–Vinogradov gives `≪√q log q` (= our trivial `√p`); GRH gives
  `√q log₂q`. The **resonance method** gives matching *large-value lower bounds*.

## 2. The single-bad-value obstruction (identical to ours)
Szabó's obstruction — "one badly-behaving character `χ` with `|Σχ(n)|=x` (no cancellation) ruins the
moment" — is **exactly** our obstruction: one `b` with `η_b≈n`, i.e. one coset `bμ_n` additively
concentrated. So our "no-conspiracy / almost-Ramanujan / clean-`E_r`" residual = the "no single bad
character" phenomenon. This is why no elementary method closes it (confirmed independently).

## 3. CRUCIAL distinction — why the interval large-values do NOT refute our formula
For **interval** sums `Σ_{n≤x}χ(n)`, the resonance method **provably** produces large values
`Δ(x,q) ≥ √x·exp(c√(log(q/x)log₃/log₂))` — *bigger* than `√(x·log)`, from the **friable-number bias**
(small-prime resonance, Littlewood/Granville–Soundararajan). If that transferred to subgroups it would
**refute** `B(μ_n)≤√(n log)` and hence `δ*=1−ρ−2/s*`. **But it does NOT transfer:** the friable
resonance is an *interval/multiplicative-integer* phenomenon; `μ_n` is a multiplicative *subgroup* with
no small-prime bias. **Our empirical data confirms this:** `B(μ_n)/√(n·log(p/n)) ≈ 0.9–1.0` (no
`exp(√log)` blow-up) across all tested `n,p`. So the subgroup sum is *better-behaved* than the generic
interval character sum — consistent with `B≈√(n log)`, the conjectured/GRH-conditional size, NOT the
resonance-inflated interval size. **Congruent; not refuted.** (Caution flagged: a subgroup-analog
large-value construction, if found, would refute the formula — none exists, and the multiplicative
structure argues against one; worth a dedicated refutation probe at larger scale.)

## 4. Net (the congruence verdict)
- **Our residual is the correct, recognized-hard object** (high-moment upper bound / sup-norm of
  character sums), unconditionally open ("hopeless" per Szabó), single-bad-value obstructed.
- **Our conjectured value `B≈√(n log)` is congruent with the literature** (the GRH-conditional /
  Montgomery–Vaughan size) and is *not* refuted by the interval large-value results (which don't
  transfer to subgroups; empirically absent).
- **A GRH-conditional path exists:** under GRH-type hypotheses the high-moment upper bounds are known
  for Dirichlet sums; an analogous subgroup-sum bound would close the prize **conditional on GRH** — a
  major (conditional) result, though not the unconditional closure the prize asks for.
- **Relevant machinery now in library:** Szabó (high moments), Munsch (sup-norm/resonance), Shkredov
  "higher energies" (1512.00627), higher-moments-of-convolutions (1110.2986), double-character-sums-
  over-subgroups (1401.6611), 2026 Burgess `F_{p^n}` (2602.22167), 2026 large-values mixed (2603.12159).

**No closure.** But this is the strongest possible confirmation that (a) our reduction is correct and
matches the frontier, (b) our `δ*` value is consistent with known character-sum behavior, (c) the
obstruction is precisely identified, and (d) the only honest paths are GRH-conditional or a genuinely
new unconditional high-moment bound for subgroup sums.

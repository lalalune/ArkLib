# ℓ-adic large sieve / effective Deligne for M(n): the DIMENSION OBSTRUCTION (#407, 2026-06-13)

Assigned angle: can Kowalski's ℓ-adic **large sieve** / the **effective form of Deligne
equidistribution** bound the **SUP** `M(n) = max_{b≠0}|η_b|` (not merely the count
`#{|η_b|>T}`) in the prize regime `n ≪ √p`? Work the conductor/dimension factors explicitly and
decide whether `q^{-1/2}·conductor` beats the Wick value to depth `r ≈ ln q`. This is the
geometric route to form (c) (`conductor of the r-fold convolution ≤ K^r`).

**Verdict: the route HITS A STRUCTURAL WALL, and the wall is sharp and nameable — a
DIMENSION OBSTRUCTION that is vacuous EXACTLY in the prize regime.** Two independent, rigorous
findings below, both numerically verified.

---

## Finding 1 — the large sieve in the frequency variable `b` is ALREADY SATURATED (exact, no slack)

The 2r-th moment in `b` is an **elementary additive count**, not a nontrivial ℓ-adic character
sum. With `η_b = Σ_{x∈μ_n} ψ(bx)`:

```
Σ_{b∈F_p} |η_b|^{2r} = Σ_{x_1..x_r,y_1..y_r ∈ μ_n} Σ_{b∈F_p} ψ(b·(Σx_i − Σy_j))
                     = q · #{(x,y)∈μ_n^{2r} : Σx_i = Σy_j in F_p}  =  q · E_r(μ_n).
```

Verified exactly (n=8, p=233, r=1,2,3: `Σ_b|η_b|^{2r} = q·E_r` to machine precision,
`/tmp/ls8.py`). The b-sum is pure additive orthogonality (`Σ_b ψ(bZ) = q·[Z=0]`); it produces
the **exact** energy count with **zero** Deligne/Weil slack. So:

- The bare large sieve (= Parseval, r=1) gives only `Σ_{b≠0}|η_b|^2 = qn − n² ⟹ max|η_b| ≤ √(qn)`,
  i.e. `√q·√n` — **vacuous** (off by `√q = 2^60` from the `√(n log p)` target). An L²-over-index
  inequality cannot see the sup beyond the average.
- The amplified (2r-th moment) sieve reduces **exactly** to "is `E_r(μ_n) ≤ (2r−1)‼·n^r(1+o(1))`
  for `r ≈ ln q`?" — **which is the open problem itself (form (b))**. There is no large-sieve
  cancellation hiding inside; the sieve is saturated.

The "conductor/Deligne" content lives **one level deeper**, in the multiplicative (Gauss-sum)
expansion `η_b = (1/f)Σ_s χ̄_s(b)g(χ_s)`, `f=(p−1)/n`. Re-expanding `E_r` there gives
`q·E_r = (q/f^{2r})·Σ_{tuples} G`, splitting into:
- **diagonal/Wick** (`{s_i}={t_j}` multiset matchings): reproduces `q·(2r−1)‼·n^r` exactly
  (sanity-checked analytically, `/tmp/largesieve_analysis.py`);
- **spurious** (`Σs_i ≡ Σt_j mod f`, `{s}≠{t}`): `#spurious ~ f^{2r−1}` Gauss-sum monomials
  `G = Πg(χ_{s_i})Πḡ(χ_{t_j})`, each of modulus `q^r`, with **no remaining variable to sum**.

So the entire prize reduces to bounding the fixed number `S = Σ_{spurious} G = q^r·Σ e^{iΘ}`,
`Θ(s,t) = Σ arg g(χ_{s_i}) − Σ arg g(χ_{t_j})`. **Square-root cancellation in S
(`|S| ≤ q^r√(#spurious)`) ⟺ joint equidistribution of the Gauss-sum ARGUMENTS** — this is
exactly Katz/Rojas-León (arXiv:2207.12439), **proven as q→∞, OPEN effectively at fixed q.** It
is the open assumption, not a theorem one may invoke: Route A is circular.

(If one *grants* square-root cancellation, it is lavishly enough: analytically
`sqrtc/target = 1/(√f·(2r−1)‼)`, so the spurious term sits a factor `√f·(2r−1)‼ ~ 2^45`
*below* the Wick value for all `r ≤ ln q`, `/tmp/ls5.py`,`/tmp/ls6.py`. The bound is true with
enormous margin — the gap is purely that the cancellation is unprovable effectively.)

---

## Finding 2 — the DIMENSION OBSTRUCTION: effective Deligne needs `f ≤ √q`, i.e. `n ≥ √p`

Where the large sieve *genuinely* could apply is the **character family** — the `f`-dimensional
torus of Gauss sums `{g(χ_s)}_{s∈Z/f}` whose geometric monodromy is `GL(1)^f` (Rojas-León Cor 7,
only Hasse–Davenport relations). Effective Deligne equidistribution of an `N`-parameter family
has discrepancy `~ N/√q` (the Weil-II / Katz discrepancy: a sum of `N` irrep-frequencies each
saving `q^{-1/2}`). At depth `r` the relevant rank is `d_r = binom(f+r−1,r) ~ f^r/r!`, giving

```
discrepancy_r ~ d_r / √q ~ f^r / (r!·√q).
```

This is `< 1` (effective) **iff** the family is under-dimensioned, `f ≲ √q`. But here `f = (p−1)/n`:

```
effective  ⟺  f ≤ √q  ⟺  (p−1)/n ≤ √p  ⟺  n ≳ √p.
```

**The prize regime is EXACTLY `n ≪ √p` (β ≥ 4 ⟹ n = p^{1/4} ≪ p^{1/2}).** So the Gauss-sum
family is **over-dimensioned for effective Deligne precisely in the prize regime**:
`f = p/n = p^{3/4} ≫ √p = p^{1/2}`, over-dimensioned by a factor `√p/n = √q/n` (exactly `n` when
β=4, since then `√p = n²`). The discrepancy `f^r/(r!√q)` is `≫1` for **every** `r ≥ 1`
(`/tmp/ls9.py`: `log10 ≈ 36, 115, 246, … 2106` at `r = 2,5,10,…,83`). The effective ℓ-adic
large sieve / Katz equidistribution is **structurally vacuous in the prize regime, at all depths**.

This is the geometric *mirror* of the additive-combinatorial wall: BGK/Shkredov need `n` large
(thin-subgroup sum-product saves more for fatter `n`); Deligne needs `n ≥ √p` (under-dimensioned
family). Both want the *opposite* of the prize regime `n ≪ √p`. The prize sits in the gap where
**neither** machine is effective. The qualitative `q→∞` theorem (Katz) does not transfer because
"`q→∞` with `n` fixed" pushes `n/√p → 0` slower than the family dimension `f/√q = √p/n → ∞` grows
— in the prize regime the two limits pull apart.

---

## Reconciliation with the `K ≈ 1.28` conductor probe (no contradiction)

`probe_conductor_prize_regime.py` measured an *empirical* "conductor base" `K_eff ≈ 1.28`. That
is an **energy-excess** base extracted from `E_r ≈ Wick·(1+ε)`, `K_eff := (ε√q)^{1/r}` — it
measures that `E_r` *happens* to be near-Wick generically. It is **not** a geometric conductor and
does **not** certify a Deligne bound. Even at the probe's small primes `f/√p = n > 1` (n=16→16,
n=32→32, n=64→64; `/tmp/ls10.py`), so the dimension obstruction holds there too. Healthy numerics
are fully consistent with: the bound is **TRUE** but **unprovable by this geometric route**.

---

## Honest bottom line

- **No advance to the open core.** The large sieve in `b` is exactly saturated (gives `q·E_r`,
  the open count). The large sieve in the character family is structurally vacuous in the prize
  regime by a clean **dimension obstruction `n ≥ √p`** that the prize regime violates by
  construction.
- **What is genuinely new here (a formalizable BRICK, documentation-level):** the precise,
  named threshold — *effective ℓ-adic Deligne for this family requires `n ≳ √p`; the prize regime
  `n ≪ √p` is exactly its complement* — with the over-dimensioning factor `√p/n` ( `= n` at β=4)
  computed explicitly. This sharpens the in-tree `MonodromyConductorScaffold.ConductorGeometricBound`
  /`KatzEffectiveGaussSum.EffectiveConductorBound` "K=O(1)" hypothesis: that hypothesis is not just
  "open," it is **provably out of reach of the generic effective-Deligne mechanism in the prize
  regime** — the `K^r√q` error in `EffectiveConductorBound` would need `K^r·√q ≤ Wick`, but the
  honest geometric error is `f^r/r!·√q`, not `K^r√q`, and `f^r ≫ q^{r/2}` here.
- **Consistent with all DEAD ENDS:** this is the geometric realization of "Katz–Sato–Tate
  inapplicable (unbounded growing support)" — the *growing support* is precisely the
  *over-dimensioning* `f = p/n → ∞`.

Files: analysis `/tmp/largesieve_analysis.py`,`/tmp/ls5–ls10.py`; exact identity verified
`/tmp/ls8.py`. Reduces to: Katz/Rojas-León joint Gauss-sum-argument equidistribution, effective
at fixed `q` — the recognized open core (= form (c)/(d)), with the new precise statement that the
**generic** Deligne route to it is dimension-obstructed in the prize regime.

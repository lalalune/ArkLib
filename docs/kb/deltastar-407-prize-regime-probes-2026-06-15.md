# #407 prize-regime probe session — BGK floor brackets + escape-attack harvest (2026-06-15)

Numeric + Lean contributions from the escape-attack workflow session. All probes exact (FFT /
exact enumeration, no sampling); all Lean bricks axiom-clean (`[propext, Classical.choice,
Quot.sound]`, real `lake build` green). Honesty contract held — refutations are successes; nothing
here closes δ\*.

## 1. The BGK floor `M(n) = max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ C√(n·log(p/n))`, bracketed

Three probes (`scripts/probes/issue407-escapes/`) pin where the floor lives and where the data
runs out — which is exactly the BGK open boundary.

- **`probe_v2_gating.py` — REFUTES the "choose `v₂(p−1)=μ` (odd index `m`) for closure" crack.**
  Bucketing primes `p≡1 (mod n)` by `t = v₂(p−1) − μ`, the ratio `R = M/√(n log(p/n))` is bounded
  ~1.2–1.5 and flat in `n` in **every** bucket; the odd-`m` bucket (`t=0`, the prize-choosable
  regime) is **not** specially tame. So one cannot close the floor by restricting the field's
  2-adic valuation. (Re-confirms structured-prime spikes >√2, e.g. R=2.06 at p=7937.)

- **`probe_const_index.py` — constant index, `n→∞` (the prize's defining feature).** At fixed
  *small* `m`, `R` is bounded and flat-to-**decreasing** (m=2 Fermat to n=2¹⁵: R 1.04→0.85; m=6 to
  n=2¹⁷: R≈1.09). Looked floor-favorable — but see §2.

- **`probe_alpha.py` — effective exponent `α(m) = d log M / d log n`.** Floor ⟺ `α = ½`. At clean
  computable scale (m=2,4; n up to 2¹⁴⁻¹⁵; 3 points) **α ≈ 0.47–0.48 < ½** — `M` is *sub*-√n,
  floor-comfortable. Larger-`m` buckets have only 2 points each (constant-large-`m` primes
  `n·m+1` are Fermat-sparse) → noise-dominated by structured spikes, no clean per-`m` trend.

## 2. The joint limit `(n→∞, m→∞)` — the genuine prize corner (self-correction)

`probe_2d_extrap.py` pools 175 `(n,m)` points and fits
`log R = 0.178 − 0.0113·log₂n + 0.0089·log₂m + 0.00206·(log₂n)(log₂m)`.
The **cross-term is positive**: the effective `n`-slope of `log R` is `−0.0113 + 0.00206·log₂m`,
negative only for `m ≲ 2⁶`, **positive at the reachable `m ~ 2¹⁶⁻²²`** where `R` already grows in
`n`. So the §1 const-index *small-m* decrease is an **edge artifact** — toward the prize (large `n`
*and* large index `m=2¹²⁸`) the limits couple positively. This independently corroborates the
parallel-session "the real signal is the COUPLING" (#407 c.212) and the "C-creep
`≈0.457 + 0.431√log n`" (c.172). **The const-index floor-survival reading is retracted.**

**Net bracket:** the data robustly shows floor-*survival* at computable scale (R bounded, α<½), but
the coupling/creep is a tiny second-order effect (`d≈0.002`) that is real in the pooled fit yet
**not resolvable per-`m` at reachable scale**, and the linear extrapolation to `m=2¹²⁸` over-shoots
the trivial `M ≤ n` ceiling — so the joint-limit fate is **undecidable from M(n) data**. That
undecidability *is* the BGK / Paley-graph wall.

## 3. B1 (R-thin / realizability) — convergent no-go, landed

The escape-attack workflow (6 angles × 3 adversarial lenses) verdict: B1's realizability/rank/sparse
machinery makes the agreement **SET** small & char-free, but that is the *non-binding* object; δ\*
gates the bad-**SCALAR SUMSET** `|S^{(+r)}|` via Vieta `γ = −e₁(S) = −∑_{x∈S} x` at depth `r≈log q`
= Glibichuk–Konyagin / BCHKS 1.12 / BGK. Binding direction settled for the low-exponent `x^k` (CS25
Cor 1, in-tree `FarThresholdMaximality`).

Landed `Frontier/_VietaScopeGapNoGo.lean`: `badScalar_eq_neg_e1` (Vieta pin) +
`sumset_card_not_determined_by_card` (countermodel `{0,1,2}` vs `{0,1,3}`: equal card, `|S+S|` = 5 vs
6 ⟹ set-cardinality is information-theoretically blind to the sumset δ\* gates). Also landed this
session: `_RThinResidueDegree.lean` (excess = residue-factor degree, n-independent k-governed — true
but on the non-binding set) and `_HankelPronyCore.lean` (Vandermonde/Prony core). **Newly ruled
out:** method-of-multiplicities (dim-1 rigidity → Johnson), Mann/Lam–Leung/Beukers–Smyth on the
agreement relation (coefficient-type mismatch — arbitrary field coeffs), Schlickewei–Evertse
isolated-count (astronomical constant).

## 4. Standing live off-BGK direction (corroborated)

The **count-lane / p-independence decoupling** (#407 c.200/c.216/c.222): over-determined far-line
incidence (`s−k ≥ 2`) is **p-INDEPENDENT** with closed form `(n/2−1)²` (k=2; n=8,16,32,64 → 9,49,
225,961), governed by a char-0 coincidence among `n`-th roots, not the p-dependent BGK max. Landed
BGK-independent levers: D3 ratio-census, count-lane `≥ centralBinom = 2^{Θ(n)}`,
`ImprimitiveSpikeStructure` (equivariance `γ↦g^{a−b}γ` ⟹ μ_{n/gcd}-coset union = the p-independence
mechanism). This is the genuine off-BGK frontier; the (n/2−1)² closed form is the next formalizable
target.

Probes: `scripts/probes/issue407-escapes/`. Bricks: `Frontier/_{VietaScopeGapNoGo,RThinResidueDegree,
HankelPronyCore,MetaTheoremSecondOrderFloor,ConvergenceHub,RThinSparseRealizability,
ChaiFanBasePanelGate,SecondMomentGapQuantified,MomentLadderExceedsPrize,MomentLadderAntitone}.lean`.

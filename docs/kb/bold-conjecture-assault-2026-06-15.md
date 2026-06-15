# Bold-Conjecture Assault on the RS Proximity-Gap Wall (#444) — 2026-06-15

**Target (the whole prize):** prove `M(n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)| ≤ C·√(n·log m)`,
`C = O(1)`, for `n = 2^μ` a PROPER multiplicative subgroup of `F_p`, `p ≈ n^4` prime (β=4, the
Burgess barrier), `m = (p-1)/n ≈ 2^128`, `μ_n` thin (`n ≈ p^{1/4}`). Equivalently: √-cancellation in
`η_b = (1/m) Σ_{χ∈H^⊥} χ̄(b) g(χ)` (a sum of `m` Gauss sums). This is the BGK/Paley thin-subgroup
√-cancellation conjecture, ~25 years open. SOTA: di Benedetto–Garaev `n^{1−31/2880} = n^{0.989}`, which
needs β<4 strictly and collapses to `n^{0.99998}` at β=4 — a full half-power gap to `n^{0.5}`.

This round assigned six FRESH domains (off the #444 §8 dead ledger). All six generators
self-reported reduction to the wall after self-refutation in the prize regime. No claimed survivors
were submitted for adversarial review. This document is the honest synthesis.

---

## 1. Did any conjecture survive as a CLOSED 9+/9+/9+/9+ statement?

**No.** Plainly: zero of the six survive as closed statements, and none scores 9+ on all four axes
(novelty, insight, proximity, feasibility). Every one reduces — by its own author's numeric refutation
in the prize regime — to the BGK/Paley sup-norm wall, the char-p depth-log moment wall, the
thin-subgroup additive-energy wall, or the EVT/two-value-spike obstruction already on the ledger. The
best proximity score achieved was 4 (bilinear), the best feasibility 3 (bilinear, rmt-no... actually 3
for bilinear/circle/rmt); none reached even 5 on proximity-or-feasibility. The prize is untouched.

---

## 2. Per-conjecture dead-ledger entries (the precise reduction/failure)

**bilinear — dyadic self-improving bilinear recursion** (nov 7 / ins 6 / prox 4 / feas 3).
The dyadic factorization `μ_n = A·B` (A = μ_√n subgroup, B = √n coset transversal) is genuine and the
balanced Cauchy–Schwarz recursion provably reaches the `n^{2/3}` ceiling (beats generic `n^{3/4}`, beats
SOTA `n^{0.989}` at small n) but **stalls exactly a half-power above the √n target**. The bold
self-improving form `M(n)^2 ≤ n·M(√n)` is numerically FALSE (ratio 1.25–2.96 at n=16,64,256): per-level
loss is **multiplicative, not additive**, so the tower does not converge to the √ floor. The inner
double-sum funnels into the **additive energy of the even-thinner subgroup `μ_{p^{1/8}}`** (E(A)~3s²) —
the SAME thin-subgroup additive-energy/BGK wall that drives SOTA and collapses at β=4, now with weaker
input.
LEDGER: *dyadic multiplicative bilinear tower recursion → n^{2/3} ceiling, reduces to additive-energy at
depth p^{1/8}, does not cross to √.* **This is the strongest of the six** (highest prox+feas) — see §3.

**padic — Adolphson–Sperber / Dwork Newton-polygon ordinary-slope forcing** (nov 9 / ins 8 / prox 2 /
feas 2). The Frobenius-eigenvalue Newton polygon of `S(b) = Σ_{x∈μ_n} e_p(bx)` is genuinely fresh and
shows a beautiful exact slope-1/2 staircase `{0, 1/m, …, (m−1)/m}` (Stickelberger valuations of the m
Gauss-sum eigenvalues), average slope → 1/2. **Fatal:** that slope-1/2 is the **Weil weight**
(`|g(χ)| = √p` each), giving only the vacuous Weil bound `√p ~ n²`; Newton = Hodge (ordinary/generic),
so AS adds nothing archimedean. Decisively, the entire p-adic valuation profile is **b-invariant** (the
phases χ_t(b) are p-adic units of valuation 0) whereas `|η_b|` spans `[~0, M]` — a b-invariant invariant
provably cannot bound a b-varying quantity. Verified incl. adversarial Fermat `2^16+1`.
LEDGER: *p-adic/Newton-polygon (Dwork/AS): NP = Hodge, slope-1/2 staircase is the Weil weight not a
cancellation slope; NP is b-invariant unit-phase, cannot see worst-case archimedean alignment → only
Weil √q, vacuous.*

**rmt — Cayley-circulant adjacency spectrum + matrix-Bernstein/Tropp** (nov 8 / ins 7 / prox 3 / feas
2). The identification `M(n) = |λ_2(Cay(F_p,+; μ_n))|` is correct, clean, fresh, and matrix-Bernstein
DOES give the exact prize shape `√(2n log p)` — but **only for a RANDOMIZED n-subset model, the wrong
object**: the deterministic arithmetic subgroup is provably heavier than a random n-subset (n=64:
M=37.4 vs random-max 27.7). For the FIXED matrix there is no randomness; the only valid deterministic
specialization is the scalar trace-exponential (log-sum-exp), whose higher-moment input
`Tr(A')^{2r}/p = Σ_b |η_b|^{2r}` at depth log m is **exactly the dead-ledger char-p moment object**, and
which degenerates to the TRIVIAL bound `√(n·max) = n` (n=64 → 64.0, not 39.9). The "matrix" gain over
the scalar moment is precisely the Golden–Thompson/Lieb step that needs INDEPENDENT summands — the
structure the subgroup lacks.
LEDGER: *RMT/matrix-Bernstein/Cayley-spectral → random model is wrong object; deterministic
trace-exponential = scalar log-sum-exp = moment route → trivial √(n·max).*

**criticality — RG/CFT fixed point at the β=4 phase transition** (nov 8 / ins 7 / prox 2 / feas 2).
FALSE on all three premises, directly in the prize regime. (i) `Q = M²/(n log m)` is **smooth through
β=4** (1.34→1.81→1.65→0.90 over β=3..6, n=64): β=4 is critical for Burgess METHODS
(`α(r)=1/4+1/(4r²)` crosses 1/4) but **not for the OBJECT M(n)** — no singular signature, no transition
to exploit. (ii) No fixed point: per-level multiplier `λ(n)=M(n)²/M(n/2)²` wanders (1.45–3.93, never
settling at 2); additive feed changes sign (+5.7 to −5.1). (iii) Dies on **decorrelation**: the two
exact dyadic branches `η_b(μ_{n/2}), η_{cb}(μ_{n/2})` have cross-correlation ρ≈0 (|ρ|<0.04
everywhere), collapsing the "renormalized" descent back to the dead naive descent + EVT two-value-spike.
Any convergent fixed point would be the trivial Gumbel law (M ≈ 1.4× iid-Gaussian max) = BGK wall
restated.
LEDGER: *RG/CFT-criticality at β=4 — DEAD: object Q smooth through β=4 (no transition); dyadic branches
decorrelate (ρ≈0) so renormalized = naive descent; no fixed point (λ wanders, feed sign-changes); any
convergent fixed point = trivial Gumbel = BGK wall.*

**circle — Hardy–Littlewood major/minor arcs on b + geometric Weyl/van-der-Corput** (nov 8 / ins 7 /
prox 3 / feas 2). Parametrizing `b = g^c` makes `η_b = Σ_j e_p(g^{c+jm})` a sum over a geometric
progression of ratio `ζ = g^m`. The minor-arc leg needs a van-der-Corput 2nd-derivative bound on
`g^{c+jm} mod p`, but that progression has **no 2nd-derivative structure** (2nd-diff uniform on
`[−1/2,1/2]`, unlike a true AP whose 2nd-diff is 0): the 2-adic self-similarity lives in the EXPONENT
lattice `mℤ` and is **destroyed by `exp ↦ g^exp mod p`** (pseudorandom). The only honest minor-arc
estimate is L²/Parseval → `RMS = √n` exactly, so the residual `M/RMS ~ √(log m)` is the BGK/Paley
sup-vs-RMS wall verbatim — circular. The "major-arc concentration" is just the Gumbel tail of m near-iid
periods, and actual M **exceeds** the iid max (Fermat amplification 1.0→1.34).
LEDGER: *circle method on b directly = L² floor + geometric-Weyl-fails (g^exp destroys exponent-lattice
self-similarity) = BGK sup-vs-RMS wall.*

**free-prob — asymptotic freeness of the dyadic halves** (nov 8 / ins 6 / prox 2 / feas 1). FAILS at
step zero. Free probability is the calculus of NON-commuting variables, but the dyadic halves
`X(b)=η_b(μ_{n/2})` and `Y(b)=η_{bζ}(μ_{n/2})` are **REAL-valued** (μ_{n/2} contains −1, so η_b is a real
cosine sum) and hence **COMMUTE**. The defining freeness 4-moment is MAXIMAL (~0.99–1.01) instead of 0 —
the polar opposite of free. The only salvage is the commutative classical CLT (data supports it:
near-independent, near-Gaussian, var = n exactly, kurtosis ~3), which gives the typical Gaussian size but
pins M only through the max-over-m-cosets uniform sub-Gaussian tail `√(2n ln m)` = the open BGK/Paley
conjecture itself (EVT crown / sub-Gaussian periods, already on the ledger).
LEDGER: *free probability requires non-commutativity the object lacks (real cosine sums commute, 4-moment
maximal); commutative CLT salvage → uniform sub-Gaussian tail = BGK wall.*

---

## 3. Partial survivor worth deeper pursuit

**bilinear (the dyadic balanced Cauchy–Schwarz recursion) is the only one worth a second look**, ranked
#1 of six. It is the sole conjecture that produces a NON-TRIVIAL unconditional exponent (`n^{2/3}`,
strictly below generic `n^{3/4}` and numerically below SOTA at small n) by a mechanism that is NOT
already on the dead ledger as a closed elimination — it reaches a genuine ceiling rather than
immediately collapsing to a known wall.

- **Why it's a partial, not a survivor:** the recursion stalls a half-power short (`n^{2/3}` not
  `n^{1/2}`), the self-improving form is numerically false (multiplicative per-level loss), and the inner
  sum funnels into the additive energy of `μ_{p^{1/8}}` — so the *closure* path is dead.
- **Why it's still interesting:** `n^{2/3}` from a self-contained subgroup-side bilinear identity (no
  external sum-product input) is a clean, reproducible artifact. The open question it sharpens: *can the
  multiplicative per-level loss be converted to additive by a smarter choice of transversal B (or a
  non-balanced split) that breaks the `E(μ_{p^{1/8}}) ~ 3s²` funnel?* That is the precise place where the
  recursion meets the wall, and it is a more concrete target than "prove BGK." Recommended as a
  scratchpad lead only, **not** a candidate (prox 4, feas 3 — far below the 9+ bar).

Ranking of the six by (prox + feas): **bilinear (7) > circle (5) = rmt (5) > padic (4) = criticality (4)
> free-prob (3)**. By novelty: padic (9) leads; by insight: padic (8) leads. The most *instructive
refutations* (cleanest new ledger geometry) are **padic** (b-invariant unit-phase NP cannot see
archimedean alignment) and **free-prob** (commutativity kills the framework at step zero).

---

## 4. Net verdict

**The prize is still the open BGK/Paley thin-subgroup √-cancellation wall. No fresh domain cracked it.**
All six conjectures reduce — by their authors' own numerics in the β=4 prize regime — to one of the
four ledger walls:

- **BGK/Paley sup-vs-RMS** (circle, free-prob salvage, criticality fixed-point limit),
- **char-p depth-log moment / trace-exponential** (rmt deterministic specialization),
- **thin-subgroup additive energy** (bilinear inner sum at `μ_{p^{1/8}}`),
- **Weil-weight vacuity / b-invariance** (padic).

The recurring structural lesson across all six: any method that is either (a) b-invariant (padic), (b)
relies on independence/randomness the deterministic subgroup lacks (rmt, free-prob, criticality
decorrelation), or (c) only achieves L²/RMS control (circle, energy routes), **cannot** reach the
archimedean worst-case `b`-alignment that defines `M(n)`. The needed √-cancellation is a purely
archimedean L²→L∞ phase-alignment phenomenon at depth `log m`, and every fresh framework here is
orthogonal to it or funnels into a thinner-subgroup version of the same wall.

Six clean dead-ledger entries added; one partial lead (bilinear `n^{2/3}` ceiling) flagged as a
scratchpad target, not a candidate. The honest bottom line stands: **prize untouched, BGK/Paley wall
intact.**

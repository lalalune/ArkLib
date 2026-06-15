# δ* (#407) Cross-Domain Reading List — OTHER fields applied to the open core

**Date:** 2026-06-14. **Lane:** S2-papers-otherdomains. **Author:** sub-agent (citations verified
against arXiv/journal; PDF bodies where unparseable are flagged, claims taken from
abstract/structured search only). **Companion:** `deltastar-407-reading-list-gaussperiods.md`
(the analytic-NT SOTA: BGK/HBK/Shkredov/di-Benedetto — that file owns the direct number-theory line;
this file owns the **cross-domain transfer** question).

## The open core (one line)

Prove a √-cancellation sup-norm bound for the thin 2-power Gauss period:
```
M(μ_n) := max_{b≠0} | Σ_{x ∈ μ_n} e_p(b x) |  ≤  C·√( n · log(p/n) ),    n = 2^μ,  n | p−1,  p ≫ n³  (prize: n < p^{1/4}).
```
Trivial bound `M ≤ n`; target closes the `n^{1/2}` gap. SOTA in the prize band is `M ≤ n^{1−o(1)}`
(BGK, ineffective) — off by the full half-power. **This file asks: does ANY other field's machinery
transfer to deliver `√n` (or a useful structural input)?** Honest headline: **none transfers as a
bound; two give useful structural inputs / no-go clarity.** Per-domain below.

---

## DOMAIN 1 — DYNAMICAL SYSTEMS (cocycle Lyapunov / large deviations)

**Motivating hope:** the in-tree 2-adic dilation recursion `f_{i+1}(b) = f_i(b) + f_i(ζ·b)`
(`SubgroupGaussSumDilationRecursion.lean` / `…TowerL2.lean`) is a 2-term linear cocycle over the
doubling map `b ↦ ζ·b`. If it had a Lyapunov exponent λ with a large-deviation theorem (LDT), the
L²-vs-L∞ gap (the wall) might be a controllable LDT tail.

### Paper 1.1 — Duarte–Klein, *Lyapunov Exponents of Linear Cocycles: Continuity via Large Deviations* (Atlantis Press, 2016); survey **`DK-survey16.pdf`** (silviusklein.github.io)
- **Verified.** Survey of LDT for linear cocycles: avalanche principle, subharmonicity, Cartan
  estimates, Hölder continuity of λ.
- **Transfer assessment — NO (verified, decisive).** Fetched the survey body: LDT for cocycles
  **fundamentally requires an ergodic / measure-preserving base** (shift, irrational rotation, i.i.d.
  or Markov forcing) to even *define* the Lyapunov exponent (Birkhoff/Furstenberg–Kesten) and its
  large-deviation tail. The δ* recursion is a **single deterministic finite orbit** of the doubling
  map with **no invariant probability measure / no randomness** — it falls outside the framework
  entirely. There is no "large deviation of one deterministic orbit." This is the rigorous version of
  the in-tree refutation that the uniform one-step phase descent (ratio 1.56 > √2) is false
  (`_DyadicPhaseChainingSubmaxRefuted.lean`): the per-level gain is `2` (L∞ triangle), not `√2`, and
  no spectral/Lyapunov averaging is available to recover `√2` deterministically.

### Paper 1.2 — Bourgain–Goldstein–Schlag line; e.g. *Large deviation estimates for quasi-periodic Gevrey cocycles* (arXiv:2509.21727, 2025)
- **Verified (exists).** Modern LDT for quasi-periodic cocycles over a Diophantine rotation.
- **Transfer assessment — NO.** Same obstruction as 1.1, sharper: these need an analytic cocycle over
  an *irrational rotation of the torus* (Diophantine frequency). The doubling map `b ↦ 2b mod n`
  on `Z/n` (n = 2^μ) is the opposite of Diophantine — it is the **fully resonant / periodic** dynamics
  (every orbit is finite, period | μ). The whole LDT theory degenerates. **Flag: dead lane** — but it
  cleanly explains *why* the L²→L∞ gap is structural, not a missing tail estimate.

> **Domain-1 verdict:** machinery is real and powerful but categorically inapplicable (no ergodic
> base). It *confirms* the wall is not a soft probabilistic tail one can sharpen. No transfer.

---

## DOMAIN 2 — ADDITIVE COMBINATORICS (vanishing sums of roots of unity, cyclotomic-integer size)

**Motivating hope:** `Σ_{x∈μ_n} e_p(bx)` is the image mod p of a cyclotomic integer
`α_b = Σ_{x∈μ_n} ζ_p^{bx}` (a sum of n roots of unity). Quantitative theory of *vanishing* and *small*
sums of roots of unity might (a) characterize when the sum is small, or (b) lower-bound it.

### Paper 2.1 — Conway–Jones, *Trigonometric Diophantine equations (On vanishing sums of roots of unity)*, Acta Arith. 30 (1976) 229–240; and **arXiv:math/9511209** (Lenstra/related exposition, verified)
- **Verified.** **Theorem (Conway–Jones):** if `Σ a_i ξ_i = 0` is a *minimal* vanishing sum of `N`
  roots of unity (no nontrivial vanishing subsum), `m = lcm(ord(ξ_i/ξ_1))`, then `m` is **squarefree**
  and `Ψ(m) ≤ N`, where `Ψ(m) = 2 + Σ_{p|m} (p−2)`.
- **Transfer assessment — STRUCTURAL INPUT, not a bound (already known-relevant).** The squarefree-`m`
  conclusion is the engine behind the in-tree **dyadic Lam–Leung / antipodal-closure** results
  (`Q1ClaimADyadic.lean`, `CyclotomicVanishingSumACL.lean`, `LamLeungTwoPow.lean`): for `n = 2^μ` the
  conductor is a 2-power so `m` squarefree forces the **only** vanishing-sum mechanism to be
  **antipodal pairing** `x ↦ −x`. This is genuinely used (char-0 `e_1(S)=0 ⇔ S=−S`). **But it is about
  EXACT vanishing over ℂ, not the SIZE of a nonzero sum, and not mod p.** It does not bound `M(μ_n)`;
  it classifies the kernel. Useful, already in the tree, **does not close the prize.**

### Paper 2.2 — *The exceptional set in Cassels' theorem on small cyclotomic integers* (arXiv:2510.20435, 2025); building on **Cassels (1969)** and **Loxton (1972)**
- **Verified.** Cassels height `M(α) = avg over conjugates β of |β|²`. Loxton's lower bound: for `k>log2`
  there is effective `c` with `M(α) ≥ c·N·exp(−k·log N / log log N)`, `N = N(α)` = min # of roots of
  unity summing to `α`. A concave `g` with `M(β) ≥ g(N(β))` for all cyclotomic `β`.
- **Transfer assessment — NO (wrong functional; verified the mismatch).** Two fatal gaps for the prize:
  (i) `M(α)` is an **average over Galois conjugates**, i.e. essentially the *root-mean-square* `√(E|β|²)`
  of all conjugates — NOT the **single conjugate** `|α_b|` we reduce mod p, and NOT the **max** over
  conjugates. A lower bound on the average says nothing about the one conjugate whose mod-p image is
  `S_b`. (ii) These are bounds in ℂ; the prize sum lives **mod p**, where `α_b` can be a unit-size
  cyclotomic integer whose residue is anything. (iii) Direction: Loxton/Cassels *lower*-bound size; the
  prize needs an *upper* bound on the max. **No transfer.** (Documented because it is the natural
  "is there a size theorem for sums of roots of unity?" question — answer: yes, but the wrong average,
  the wrong field, and the wrong direction. Mirrors the in-tree §5.0 Mahler/Littlewood KILL: the
  norm/house route is tight and cannot give `|N| < p`.)

### Paper 2.3 (sum–product backbone) — Bourgain–Konyagin / *Sum-product phenomena in F_p: a brief introduction* (Garaev, arXiv:0904.2075)
- **Verified.** The additive-combinatorics route to subgroup character sums (the BGK proof technique).
- **Transfer assessment — this IS the prize route, and it is the one that stalls at `n^{1−o(1)}`.**
  Listed for completeness: the sum–product method (Plünnecke–Ruzsa + multiplicative energy) is exactly
  what BGK uses; it is ineffective for thin subgroups (see companion file). **No new transfer beyond the
  known SOTA.**

> **Domain-2 verdict:** Conway–Jones is a real structural input (already exploited in-tree, classifies
> the vanishing kernel, doesn't bound size). Cassels/Loxton is the wrong functional (avg conjugate,
> lower bound, char-0). Sum-product is the open route itself. No closure.

---

## DOMAIN 3 — ALGEBRAIC GEOMETRY (Weil II / ℓ-adic monodromy for short μ_n sums)

**Motivating hope:** Deligne's Weil II + Katz monodromy give square-root cancellation for *complete*
sums attached to a sheaf on a curve. Is there a sheaf whose Frobenius trace is the `μ_n` sum, with the
sum being "complete" so Weil II gives `√n`?

### Paper 3.1 — Ostafe–Shparlinski–Voloch, *Weil Sums over Small Subgroups*, Math. Proc. Camb. Phil. Soc. 176(1) (2024) 39–53; **arXiv:2211.07739** (2022)
- **Verified (journal + arXiv).** Abstract (verbatim sense): new bounds on **short Weil sums over small
  multiplicative subgroups** that are **nontrivial in the range where the classical Weil bound is
  already trivial**, via a **blend of algebraic geometry and additive combinatorics**.
- **Transfer assessment — PARTIAL / FLAGGED, most likely NO (could not fully verify degree restriction
  from PDF; abstract verified).** This is the single most on-target algebraic-geometry paper: it is
  *exactly* "Weil sums over small subgroups." BUT: it bounds `Σ_{x∈H} ψ(f(x))` for **polynomials/
  Weil sums** where the AG input (curve genus / monodromy of `f`) provides cancellation that
  additive-combinatorics then extends below the Weil threshold. The **prize sum is the LINEAR monomial
  `f(x)=bx`** (the pure Gaussian period) — which has **no nonlinear AG content**; for linear `f` the
  problem collapses *back onto BGK* (the additive-combinatorics half), the open `n^{1−o(1)}` regime.
  So OSV's beyond-Weil gain comes from the nonlinear `f`, which the prize does not have. **Honest flag:
  worth one careful read of Thm 1.1 to confirm whether ANY linear-`f` corollary beats `n^{1−o(1)}`
  (I could not parse the PDF body; the abstract + the "AG+additive" method strongly indicate the gain
  is nonlinear-only). If it did, it would be directly prize-relevant — hence flagged, not dismissed.**
- Companion same group: *Equations and character sums with matrix powers, Kloosterman sums over small
  subgroups and quantum ergodicity* (arXiv:2110.10941, IMRN 2023) — verified; Kloosterman (bilinear),
  not the linear Gauss period; same nonlinearity caveat.

### Paper 3.2 — Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups* (Annals Studies 116, 1988); and *Equidistribution and independence of Gauss sums* (Rojas-León, **arXiv:2207.12439**, 2022/24)
- **Verified.** Katz: the rank-2 Kloosterman sheaf on `G_m`, big geometric monodromy ⇒ vertical
  Sato–Tate for Kloosterman/Gauss sums. Rojas-León: independent equidistribution of Gauss sums of
  monomials, relations only from conjugation / Hasse–Davenport.
- **Transfer assessment — NO (dimension obstruction; matches in-tree large-sieve KILL).** Weil II /
  Katz equidistribution is **as `q → ∞` with the sheaf of FIXED rank/dimension**. To "see" the `μ_n`
  sum geometrically as a complete sum with `√n` cancellation you need the relevant variety dimension to
  scale with `n`, i.e. effectively `n ≳ √p` (the sieve/monodromy needs the subgroup comparable to the
  field). The prize has `n ≪ p^{1/4}` — **vacuous at every depth** (this is exactly the recorded
  `deltastar-407-large-sieve-dimension-obstruction` and `…katz-monodromy-research` KILL: needs `n ≳ √p`,
  prize is `n ≪ √p`). Equidistribution gives the *typical/average* sum, never the **deterministic max**
  over a thin designed subgroup. **No transfer.**

> **Domain-3 verdict:** OSV "Weil sums over small subgroups" is the right title but its beyond-Weil gain
> is **nonlinear-`f`-driven**; the prize's linear monomial falls back on BGK. **FLAG OSV Thm 1.1 for a
> careful read** (only paper here with a nonzero chance). Katz/Weil-II monodromy is dimension-obstructed
> (needs `n ≳ √p`) — re-confirmed dead. No closure.

---

## DOMAIN 4 — RANDOM MATRIX / PROBABILISTIC (Gaussian-period value distribution)

**Motivating hope:** if the `μ_n` sum value behaves like a sum of `n` independent unit-circle steps,
its max over `b` would be `√(n log n)` (extreme-value of a random walk) — exactly the target shape.
Does any RMT/equidistribution theorem rigorously establish this?

### Paper 4.1 — Duke–Garcia–Lutz, *The graphic nature of Gaussian periods*, Proc. AMS 143(5) (2015) 1849–1863; **arXiv:1212.6825**
### Paper 4.2 — Kowalski–Untrau, *Ultra-short sums of trace functions*, Acta Arith. (2023); **arXiv:2302.13670**
- **Both verified.** DGL: supercharacter framework, limiting *measures* for Gaussian-period plots.
  Kowalski–Untrau **generalizes DGL** and gives the precise statement: for `g = X^d − 1` (d-th roots of
  unity) the normalized sum **converges in law to `X_1 + … + X_d`, a sum of `d` INDEPENDENT
  uniform-on-the-circle random variables** (the random walk) — verified verbatim from structured search
  of the paper.
- **Transfer assessment — NO, but it is the SHARP statement of why (the most important entry here).**
  The random-walk picture is **literally true** — but in the regime where the number of summands
  `d` is **FIXED while `q → ∞`** (`d` = the period length / index, held constant). In the prize the
  number of summands is `n = 2^μ` which **GROWS** with `p`. The theorem's hypotheses (and the Sato–Tate
  / Deligne equidistribution behind them) are an `q → ∞` statement at **fixed `d`**; they say *nothing*
  about the deterministic **max over `b`** when `d = n` grows. Concretely:
  - DGL/KU give the *distribution* of one normalized value for fixed small index — a CLT/random-walk law.
  - The prize needs `max_b |S_b| ≤ √(n log)` **for a single fixed large `p`** with `n` large — a
    deterministic extreme-value statement, NOT an `q→∞` fixed-`d` distributional limit.
  This is the precise sense in which "the truth looks like a random walk" (the target `√n` is the random
  walk scale) but **no theorem proves the deterministic thin-subgroup sum IS a random walk** — that gap
  IS the prize. **Honest flag: this is the best heuristic justification for the `√n` target and pins
  exactly what must be proven (a quantitative, uniform-in-`b`, growing-`n` version of KU). No transfer
  as-is, but it is the cleanest statement of the goal.**

### Paper 4.3 — Habegger, *The Norm of Gaussian Periods*, Q. J. Math 69(1) (2018) 153––; **arXiv:1611.07287**
- **Verified.** Asymptotics of the **absolute (algebraic) norm** `|N(η)| = Π_conjugates` of a Gaussian
  period of **fixed odd length** — a case of **Myerson's conjecture** — via Bombieri–Masser–Zannier
  unlikely intersections + o-minimality.
- **Transfer assessment — NO (norm = product over conjugates, not the single sup).** Same functional
  mismatch as Cassels (2.2): the *norm* is a product over all conjugates, the prize needs the *sup of
  one* (or its mod-p residue). Fixed length, char 0. **No transfer**, but documents that even the
  best "size of a Gaussian period" results target the norm/average, never the deterministic sup of a
  thin subgroup — reinforcing that the sup-norm `M(μ_n)` is genuinely the open object.

### Paper 4.4 (function-field RMT, adjacent) — Gorodetsky–Rodgers, *Equidistribution of high traces of random matrices over finite fields and cancellation in character sums of high conductor*, **arXiv:2307.01344** (2024)
- **Verified.** `Tr(g^k)` for `g ∈ GL_n(F_q)` equidistributes iff `log k = o(n²)`; reduces to
  cancellation in **short character sums in `F_q[T]` (function fields)**.
- **Transfer assessment — NO (function field, wrong arithmetic).** Genuinely an RMT⇆character-sum-
  cancellation bridge, but in the **`F_q[T]` function-field** world; the prize is **prime field `F_p`**.
  The function-field RMT bridge (deep monodromy of GL_n) has no prime-field analogue for thin `μ_n`.
  Listed as the closest RMT-↔-cancellation theorem in existence — confirms the *kind* of statement that
  would close the prize exists in function fields but not in the prime-field thin-subgroup setting.

> **Domain-4 verdict:** Kowalski–Untrau is the **sharpest articulation of the target** (sum = random
> walk of `d` steps ⇒ max `≈ √(n log)`), but it is a **fixed-`d`, `q→∞`** distributional limit; the
> prize needs **growing-`n`, fixed-`p`, deterministic max**. Habegger/Cassels target the wrong
> functional (norm/average). Gorodetsky–Rodgers is the right bridge in the wrong (function-field) world.
> No transfer; best heuristic anchor for `√n`.

---

## CONSOLIDATED CROSS-DOMAIN VERDICT (honest)

| Domain | Best paper(s) | Could it give `√n`? | Status |
|---|---|---|---|
| Dynamical systems (cocycle LDT) | Duarte–Klein; BGS quasi-periodic LDT | NO — needs ergodic base; recursion is deterministic+resonant | dead, but explains the structural wall |
| Additive comb. (vanishing sums) | Conway–Jones; Cassels/Loxton | NO as bound — CJ classifies kernel (used in-tree); Cassels = wrong avg, wrong direction | CJ = real structural input (already exploited); rest no |
| Algebraic geom. (Weil/monodromy) | **Ostafe–Shparlinski–Voloch 2024**; Katz; Rojas-León | Katz NO (dim obstruction `n≳√p`); **OSV FLAGGED** (beyond-Weil gain is nonlinear-`f`; prize is linear) | Katz dead; **OSV Thm 1.1 worth one read** |
| Random matrix / prob. | **Kowalski–Untrau 2023**; DGL; Habegger; Gorodetsky–Rodgers | NO — KU is fixed-`d` `q→∞` (prize is growing-`n` fixed-`p`); rest wrong functional/field | KU = sharpest target statement; no transfer |

**Bottom line.** No cross-domain result transfers to give the `√n` sup-norm bound. The two non-trivial
yields are: **(i)** Conway–Jones squarefree-conductor structure, *already load-bearing in-tree* for the
dyadic antipodal-closure lemmas (kernel classification, not a size bound); **(ii)** Kowalski–Untrau /
DGL random-walk limit, which is the **rigorous heuristic** behind the `√(n log)` target and pins the
exact missing theorem: a **uniform-in-`b`, growing-`n`, single-prime** version of the random-walk law
for thin `μ_n` (no such theorem exists — it is the prize). **One flagged unknown deserving a deeper
read: Ostafe–Shparlinski–Voloch Thm 1.1** — confirm whether any linear-monomial corollary beats
`n^{1−o(1)}` (abstract + method suggest the beyond-Weil gain is nonlinear-only, but the PDF body was not
machine-parseable here). Every other lane re-confirms the in-tree KILLs (large-sieve dimension
obstruction, Mahler/Littlewood norm tightness, refuted one-step √2 descent). The core remains the
field-universal BGK/Paley `√n` wall.

### All citations (verified IDs)
- Duarte–Klein, *LE of Linear Cocycles: Continuity via Large Deviations*, Atlantis Press 2016 (survey: silviusklein.github.io/research/DK-survey16.pdf).
- *Large deviation estimates for quasi-periodic Gevrey cocycles*, arXiv:2509.21727 (2025).
- Conway–Jones, *Trigonometric Diophantine equations*, Acta Arith. 30 (1976) 229–240; exposition arXiv:math/9511209.
- *The exceptional set in Cassels' theorem on small cyclotomic integers*, arXiv:2510.20435 (2025); Cassels (1969); Loxton (1972).
- Garaev, *Sum-product phenomena in F_p: a brief introduction*, arXiv:0904.2075.
- Ostafe–Shparlinski–Voloch, *Weil Sums over Small Subgroups*, Math. Proc. Camb. Phil. Soc. 176(1) (2024) 39–53; arXiv:2211.07739.
- Ostafe–Shparlinski et al., *…Kloosterman sums over small subgroups and quantum ergodicity*, arXiv:2110.10941 (IMRN 2023).
- Katz, *Gauss Sums, Kloosterman Sums, and Monodromy Groups*, Annals of Math. Studies 116, 1988.
- Rojas-León, *Equidistribution and independence of Gauss sums*, arXiv:2207.12439 (2022/24).
- Duke–Garcia–Lutz, *The graphic nature of Gaussian periods*, Proc. AMS 143(5) (2015) 1849–1863; arXiv:1212.6825.
- Kowalski–Untrau, *Ultra-short sums of trace functions*, Acta Arith. (2023); arXiv:2302.13670.
- Habegger, *The Norm of Gaussian Periods*, Q. J. Math 69(1) (2018); arXiv:1611.07287.
- Gorodetsky–Rodgers, *Equidistribution of high traces of random matrices over finite fields…*, arXiv:2307.01344 (2024).

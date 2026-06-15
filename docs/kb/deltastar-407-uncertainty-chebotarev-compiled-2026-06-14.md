# δ\* via the DFT uncertainty principle — the Chebotarev mechanism, formalized (#407)

**Date:** 2026-06-14. **Status:** verified reframing + 6 axiom-clean Lean bricks; **not a closure**
(the sub-Johnson upper bound for `Z_{2^μ}` is the open core). Companion to
[`INSIGHT-smooth-domain-hardness-IS-the-uncertainty-principle.md`](INSIGHT-smooth-domain-hardness-IS-the-uncertainty-principle.md)
(the conceptual framing) — this doc adds the **mechanism (Chebotarev)**, the **Lean formalization**,
and the **8-angle bound analysis** with exact, hypothesis-checked literature.

## 1. The reformulation (VERIFIED exact)

Far-line agreement of the monomial pencil `x^a + γ·x^b` with a degree-`<k` Reed–Solomon codeword `c`
on a set `S ⊆ μ_n` is the vanishing on `S` of

```
P(x) = x^a + γ·x^b − c(x),        deg c < k.
```

As a function on `μ_n ≅ Z_n` (write `x = ζ^j`), `P` has **DFT/Fourier support**

```
supp P̂ ⊆ T := {0,1,…,k−1} ∪ {a, b},        |T| ≤ k+2
```

(for *far* directions `a,b ∉ {0..k−1}`). The scalar `γ` is only the Fourier **coefficient** at
frequency `b` — it never moves the support. Hence the far-line list-decoding radius is exactly the
**uncertainty quantity**

```
s*  =  max #zeros of P on μ_n over all such P
    =  n − min(physical support) of a nonzero (≤k+2)-Fourier-sparse function on Z_n.
```

**Verification (independent, exact):** 160/160 random `F_p` trials (`p ≡ 1 mod n`, primitive `ζ`,
exact DFT over `F_p`, no float) confirm `supp P̂ ⊆ T` with zero off-support content for
`n ∈ {8,16,17,19}`. The identity `s* = n − minSupport(T)` is confirmed by **two independent
computations agreeing exactly** — (i) the uncertainty quantity via exact rank-deficiency search of
DFT row-submatrices, (ii) brute-force `s*` over actual stacks via the affine-in-`(γ,c)` left-null
structure — on every tractable case `n = 4,5,7,8`. Probes: `up_verify.py`, `up_verify2.py`,
`up_minsupp.py`.

## 2. The mechanism — Chebotarev's theorem on roots of unity

Let `C_T` be the `[n, |T|]` linear code = column-span of the DFT minor restricted to frequencies `T`.
A `T`-Fourier-sparse function vanishing on `S` is a codeword of `C_T` supported off `S`, so

```
s*  =  n − d_min(C_T).
```

`C_T` is **MDS** (`d_min = n − |T| + 1`, giving `s* = |T| − 1 = k+1` = capacity) **iff every
`|T|×|T| minor of the DFT matrix is nonzero**. By

> **Chebotarev's theorem on roots of unity** (Tao, arXiv `math/0312398`): *all minors of the
> `n×n` DFT matrix are nonzero **iff `n` is prime**.*

**⟹ the prime → capacity / 2-power → Johnson dichotomy IS exactly the Chebotarev iff.** This is the
one-line reason the smooth `2^μ` domain is the prize's hard case: for prime `n` every DFT minor is
nonzero (MDS, capacity); for `n = 2^μ` (maximally composite) the DFT has many vanishing minors
(subgroup-supported functions vanish on large structured sets), so `C_T` is far from MDS.

## 3. The verified dichotomy (exact `s*` table)

| n | type | s\* | δ\* limit | source |
|---|---|---|---|---|
| 5,7,13,17,19,23,29,31 | **prime** | **k+1 EXACTLY** (every k) | 1−ρ **capacity** | Tao 2005, sharp |
| 8,16,32,… | **2-power** | **n/2 + (k−1)** (≫ k+1) | between Johnson & capacity | binomial extremal |

At `n=16,k=4` (ρ=¼): `s*=10`, between Johnson `√(kn)=8` and capacity `(1−ρ)n=12`. At low rate the
2-power `s*=n/2+(k−1)` is **above** Johnson `√(kn)` (factor → 3/2 at ρ=¼) — so beyond-Johnson behavior
is genuinely real, not marginal.

## 4. The formalization (6 axiom-clean Lean bricks, real `lake build`)

All audit `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`. All connect to the **real** objects
(`rsCode`, `FarFromCode`, the explicit `farLinePoly`), passing the disconnect test.

| brick | content |
|---|---|
| `Frontier/UncertaintyCapacitySidePrime.lean` | `farLine_agreement_isRoot` (agreement pt ⟹ root of the explicit sparse `farLinePoly = X^{a%n}+γX^{b%n}−P`, PROVEN); prime `s* ≤ k+1` conditional on named `TaoSparseZeroBound` ⟹ capacity. |
| `Frontier/UncertaintyTwoPowerBounds.lean` | Donoho–Stark `s* ≤ n − ⌈n/(k+2)⌉` (near-capacity, weaker than Johnson); `sStar_le_kAddOne_of_tao` (prime); named open `JohnsonFloorTwoPower`. |
| `Frontier/UncertaintyTwoPowerExtremal.lean` | `subgroupBinomialExtremal` (the binomial `x^{n/2}+c` on a μ_{n/2}-coset, 2-sparse); `sStar_subgroupBinomialExtremal`: `s*=n/2`, dominating Johnson at fixed rate. |
| `Frontier/StepanovStructuredVacuous.lean` | `stepanov_collapses_to_degree`: Stepanov multiplicity pins to `M=1` by separability of `X^n−1` ⟹ only the trivial `s* ≤ deg`. Vacuous here. |
| `Frontier/OddExcessLaw.lean` | `oddExcess_card`: `\|oddExcess\| = I_n − I_{n/2}`; `oddExcess_eq_empty_iff_collapse`. |
| `Frontier/EvenWitnessReverseCollapse.lean` | the reverse 2-adic collapse PROVEN for fibre-symmetric witnesses (the 25 descending scalars at n=16); odd 64 open. |

## 5. The 8-angle bound analysis — what each known tool gives, and where it stops

| angle | sharpest bound on `s*(2^μ, k)` | below Johnson? |
|---|---|---|
| Tao uncertainty | prime: `k+1` exact; 2-power: **inapplicable** (Chebotarev iff fails) | n/a |
| Donoho–Stark | `s* ≤ n − ⌈n/(k+2)⌉` (near-capacity) | **no** (weaker) |
| Meshulam (abelian) | collapses to Donoho–Stark for `n=2^μ` | **no** |
| Stepanov/Weil | `s* ≤ deg ≤ n−1` (M=1, separable) | **no** (trivial) |
| Cheng–Gao–Wan subgroup zero-count | vacuous at `gcd(exps, n)=1` (the `{0..k−1}` interval forces it) | **no** |
| FarThreshold degree bound | single monomial `≤ b mod n` | partial |
| **extremal (lower)** | `s* ≥ n/2 + (k−1)` PROVEN | (lower bound, above Johnson) |

**No uncertainty-principle variant yields any upper bound below Johnson `√(kn)` for `n=2^μ`.** That gap
— a sub-Johnson upper bound — is the open core, now classically stated.

## 6. The open core, classically stated

> **The quantitative uncertainty principle for `Z_{2^μ}`:** the minimum physical support of a nonzero
> `(k+2)`-Fourier-sparse function on `Z_{2^μ}` — equivalently the max #zeros on `μ_{2^μ}` of a function
> with Fourier support `{0..k−1, a, b}`. Johnson side: `√(kn)`. Conjectured floor: `k + Θ(n/log n)`.

This is **Borwein–Erdélyi / Konyagin sparse-polynomial territory** (zeros of lacunary polynomials over
roots of unity / subgroups). The next literature lever is exactly the sparse-polynomial zero-count for
the structured exponent set `{0..k−1, a, b}` on `2`-power roots of unity.

## 7. Citations (verified exact, hypotheses checked)

- **Tao (2005)**, *An uncertainty principle for cyclic groups of prime order*, Math. Res. Lett.
  12(1):121–127 (DOI `10.4310/MRL.2005.v12.n1.a11`, arXiv `math/0308286`): for `p` prime,
  `|supp f| + |supp f̂| ≥ p+1`, **sharp**; a `(k+1)`-monomial-Fourier-support function has `≤ k` zeros.
  *Applies to prime n only.*
- **Donoho–Stark (1989)**, SIAM J. Appl. Math. 49(3):906–931 (DOI `10.1137/0149053`):
  `|supp f|·|supp f̂| ≥ |G|`, equality iff `f` is a coset indicator (`χ·1_{a+H}`). *Weak for composite.*
- **Meshulam (1992/2006)**, *An uncertainty inequality for finite abelian groups*, EJC: divisor-structure
  refinement; collapses to Donoho–Stark for `n=2^μ`.
- **Chebotarev's theorem on roots of unity** (proof: Tao, arXiv `math/0312398`): all DFT minors nonzero
  iff `n` prime. **The mechanism.**
- **Bi–Cheng–Rojas (ISSAC 2013, arXiv `1204.1113`)** and **Cheng–Gao–Rojas–Wan (arXiv `1411.6346`)**:
  `t`-nomial roots lie in `≤ 2((q−1)/δ)^{1−1/(t−1)}` cosets, `δ = gcd(exps, q−1)` — the Johnson coset side.

## 8. Pitfalls recorded

- The Tao constant is `k+1` (not `k+2`): a `(k+2)`-Fourier-sparse function on a prime cyclic group has
  `≤ (k+2)−1 = k+1` zeros.
- Donoho–Stark on `2^μ` gives `s* ≤ n − n/(k+2)`, which is **near capacity, not Johnson** — it is the
  *weak* uncertainty for composite groups; the actual `√(kn)` Johnson behavior is a *different, sharper*
  phenomenon (the coset/subgroup structure), not the free-`(k+2)`-sparse uncertainty.
- Cheng–Gao–Wan is vacuous precisely because the codeword interval `{0..k−1}` forces `gcd(exps, n)=1`;
  it bites only for pure-monomial (sub)structures with a common exponent divisor.

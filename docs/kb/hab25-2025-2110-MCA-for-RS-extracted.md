# eprint 2025/2110 (Hab25) "A note on mutual correlated agreement for Reed–Solomon codes" — full extraction (#444)

Ulrich Haböck (StarkWare), Nov 17 2025. The Cloudflare-blocked paper flagged in c.4704732957 as "the most likely
published bypass." **Read in full from `~/papers/arklib/eprint-2025-2110-Hab25.pdf`. VERDICT: NOT a bypass —
it proves MCA exactly UP TO the Johnson radius, not past it.** The prize window interior remains open.

## What it proves (the headline)

**RS codes satisfy mutual correlated agreement (MCA, ACFY24 Def 1) up to the Johnson radius** `γ = 1−√(1−δ)`,
`δ = 1−k/|D|`. This CONFIRMS the ACFY24 conjecture (they had MCA up to δ/2). It does NOT reach the window
interior (past Johnson) — exactly the achievable lower endpoint, rigorously, for MCA.

## The exact quantitative bound (Theorem 2, generalizing BCI+20 Thm 5.1)

For `C = RS[F_q, D, k]`, `|D|=n`, `ρ=k/n`, and `γ = 1 − (1 + 1/(2m))·√ρ` (integer `m≥3`), the exception set
```
E = { z ∈ F_q : ∃A⊂D, |A|≥(1−γ)n, f_z|_A ∈ C|_A but [f_0,f_1]|_A ∉ C²|_A }
```
is bounded by  **`|E| ≤ (ℓ⁷/3)·(ρn)²`,  `ℓ = (m+1/2)/√ρ`.**
- **"Essentially the same bound as ordinary correlated agreement in BCI+20"** (Remark 3) — i.e. the Johnson-radius
  bound, NOT a window-interior improvement.
- As `m→∞`, `γ → 1−√ρ` (Johnson exactly) but `ℓ→∞` so `|E|→∞` (vacuous AT Johnson). So it gives MCA *approaching*
  Johnson with the exception count growing — pure Johnson-radius behavior, **zero window-interior content.**

## Method (Guruswami–Sudan over the function field)

Generalizes BCI+20 §5: run the GS list-decoder on `f = f_0 + Z·f_1` (Z a formal variable) over `K = F_q(Z)`,
analyze the GS decoder over the rational function field. The interpolation polynomial `Q(X,Y,Z)` factors
`Q = C·∏_i R_i(X, Y^{p^{f_i}}, Z)^{e_i}`; degrees `D_Y<ℓ`, `D_X<ℓρn`, `D_YZ≤(ℓ³/6)ρn`. A point `x_0` with
`disc_Y R_i(x_0,Y,Z)≠0` (exists if `|F|>ℓ²ρn`) starts the Hensel lift; refine over irreducible/Hensel factors
`E = ⋃ E_{i,j}`, each `|E_{i,j}| ≤ (ℓ⁶/3)(ρn)²`, summed over `D_Y<ℓ` factors.

## The key reusable lemma (Lemma 1, AHIV17/BKS18 — "collinearity ⟹ correlated agreement")

> Given a linear code `C`, words `f_0,f_1`, `γ∈(0,1)`, and **two** codewords `p_0,p_1` with `Δ(p_0+zp_1, f_0+zf_1)≤γ`
> for all `z ∈ S ⊆ F_q`: **if `|S| > ⌈γn⌉ + 1`, then `[f_0,f_1]` agrees with `[p_0,p_1]` on a set of density `1−γ`.**

Proof: the disagreement set `E={x:(p_0,p_1)(x)≠(f_0,f_1)(x)}`; each `x∈E` has ≤1 scalar `z` with `c_z(x)=f_z(x)`
(linear functional `c_z−f_z = p_0−f_0 + z(p_1−f_1)` nontrivial), so `|S| ≤ |E'| = e+1` — contradiction. This is the
**floor mechanism**: enough collinear proximate points (`|S|>γn+1`) *force* correlated agreement. The threshold
`|S| > γn+1` is exactly the far-line agreement-count condition the campaign's incidence object measures.

## History of MCA radii (Hab25 page 2)

| Work | MCA radius θ |
|---|---|
| ZCF23 (Basefold) | δ/3 |
| Zei24 (early) | 1−⁴√(1−δ) ("double Johnson"); later 1.5-Johnson |
| GKL24 (Gao–Kan–Li) | 1−³√(1−δ) ("one-and-a-half Johnson") |
| ACFY24 | δ/2 (conjectured up to Johnson) |
| **Hab25 (2025/2110)** | **1−√(1−δ) = Johnson (proven)** |

## Implication for the prize (#444)

- **The "published bypass" hope is ELIMINATED.** Hab25 confirms the *achievable lower endpoint* (Johnson) for MCA
  rigorously — matching the dossier's "Johnson achievable" — and provides **nothing past Johnson**. The window
  interior `(1−√ρ, 1−ρ−Θ(1/log n))` for explicit RS = the genuine open core, untouched by this paper.
- Hab25 notes a verbose update incorporating **BCH+25 (= 2025/2055)** improvements will follow — worth watching,
  but the present paper is Johnson-radius only.
- Lemma 1's `|S|>γn+1` collinearity threshold is the same far-line agreement-count the campaign's
  incidence/over-determined object measures — a clean confirmation that the floor mechanism IS the
  collinear-points-force-agreement count, exactly the lacunary/uncertainty object in lanes #3/#4.

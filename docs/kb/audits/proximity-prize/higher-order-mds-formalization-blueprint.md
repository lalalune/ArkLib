# Formalization blueprint: higher-order MDS → RS list-decoding capacity (the #141 open core)

**Status: ROADMAP / SPECIFICATION ONLY. This document contains NO proofs and NO claims of
formalized results.** It is a faithful, cited plan for the multi-paper formalization effort that
would be required to discharge the open core `UniversalGSListMassBound`
(`ArkLib/Data/CodingTheory/ProximityGap/GrandChallenge141UniformResolved.lean`). The theorems
listed here are *external research results*; none is proven in ArkLib or mathlib. Treat every
"Theorem" below as an unformalized target, and every "Definition" as a fidelity-critical item to be
checked against the cited source by a human before it is committed as Lean.

## 0. Honest scope (read first)

- The **field-universal / worst-case-RS** form of "list-decode plain RS past Johnson to capacity"
  is **FALSE**, not open: Ben-Sasson–Kopparty–Radhakrishnan construct, via subspace polynomials,
  RS codes with super-polynomial list size just past the Johnson radius `1 − √ρ`. Do **not** target
  this form; it cannot be proven.
- The **true** result is for **generic / random** RS codes (Brakensiek–Gopi–Makam, Guo–Zhang,
  Alrabiah–Guruswami–Li): generic RS codes achieve list-decoding capacity. This is what the
  apparatus below proves, and what `UniversalGSListMassBound` should ultimately be specialized to
  (a per-rate / large-field / genericity-qualified statement, **not** "all codes").
- ArkLib already has the *downstream* reduction verified: `UniversalGSListMassBound ⟹` the GC1 MCA
  prize. This blueprint covers the *upstream* coding-theory apparatus that would supply (the list
  size half of) `UniversalGSListMassBound`. The other half — beyond-UDR `FaithfulGSFamily` (#66) —
  is a separate measure-theoretic target not covered here.

## 1. The four layers (faithful statements + citations)

### Layer A — Higher-order MDS codes, `MDS(ℓ)` (definition)

Brakensiek–Gopi–Makam ([arXiv:2206.05256], building on Roth [arXiv:2111.03210]). For an `[n,k]`
code with generator matrix `G` and, for `A ⊆ [n]`, the column span `G_A`:

> `C` is **`MDS(ℓ)`** if for all subsets `A₁,…,Aℓ ⊆ [n]`,
> `dim(G_{A₁} ∩ … ∩ G_{Aℓ})` equals the **generic** value of that intersection dimension (the value
> attained by a generic `k×n` matrix).

Roth's equivalent list-decoding flavor, **`LD-MDS(L)`** ([arXiv:2111.03210]): `C` meets the
*generalized Singleton bound* for average-radius list decoding — for every `y` there are **no**
`L+1` distinct codewords `c₀,…,c_L` with `Σ_i d(c_i, y) ≤ L(n−k)`. Equivalently `C` is
`(ρ, L)`-average-radius list-decodable at `ρ = (L/(L+1))(1 − k/n)`, optimal radius `τ = L(n−k)/(L+1)`.
BGM show `MDS(L+1) ⟺ LD-MDS(L)` (nearly equivalent; check exact hypotheses in 2206.05256 §1).

**Fidelity warning:** there are ≥3 equivalent formulations (intersection-dimension, zero-pattern,
list-decoding). Pick one as primary in Lean and *prove* the equivalences; do not assume them.

### Layer B — The GM-MDS theorem

Conjectured by Dau–Song–Dong–Yuen; proved independently by **Lovett (2018)** and
**Yildiz–Hassibi (2018)**.

> **Theorem (GM-MDS).** For `q ≥ n + k − 1`, there exists an `[n,k]_q` MDS code with generator
> matrix `G` over `F_q` such that `G_{i,j} = 0` whenever `j ∈ S_i`, **iff** the support family
> `S = (S_i)` satisfies the **MDS (Hall-type) condition** (`|∪_{i∈I} S_i| ≤ Σ_{i∈I}|S_i|`-style,
> exact form per the source).

This is the algebraic engine: it certifies generic RS codes realize all admissible zero patterns.

### Layer C — Generalized GM-MDS / polynomial codes are higher-order MDS

Brakensiek–Dhar–Gopi, "Generalized GM-MDS: Polynomial Codes Are Higher Order MDS"
([arXiv:2310.12888], STOC 2024). Upgrades Layer B to higher order and **drives the field size down
to linear** in `n`. This is what makes the capacity result hold over *small* (linear-size) fields.

### Layer D — Generic RS achieve list-decoding capacity (the payoff)

> **Theorem (BGM, [arXiv:2206.05256]).** Generic Reed–Solomon codes are `MDS(ℓ)` for all `ℓ`; hence
> a generic `[n,k]` RS code is `(ρ, L)`-list-decodable up to capacity `ρ = (L/(L+1))(1 − k/n)` with
> list size `L`. Field size: exponential in the original BGM; **linear** via Layer C
> ([2310.12888]) and the improved-field-size line ([arXiv:2212.11262]); constant-size fields for AG
> codes ([arXiv:2310.12898]).

"Generic" = the evaluation points are algebraically independent / a random tuple avoids a
proper subvariety (Schwartz–Zippel-grade genericity). The capacity statement is **probabilistic
over the code**, not universal over all codes — this is the crux that reconciles with Layer 0's
BKR impossibility.

## 2. Dependency order for formalization

```
mathlib foundations (exists): linear codes, MDS/IsMDS, Vandermonde, RS codes, Schwartz–Zippel
   │
   ├─[A1] def MDS(ℓ) (intersection-dimension form)         ← fidelity-critical
   ├─[A2] generic intersection dimension (the RHS of A1)    ← new theory
   ├─[A3] def LD-MDS(L) + generalized Singleton bound       ← new theory
   ├─[A4] MDS(L+1) ⟺ LD-MDS(L)  (the bridge)               ← hard, the BGM equivalence
   │
   ├─[B1] MDS zero-pattern / Hall condition (def)
   ├─[B2] GM-MDS theorem  (Lovett / Yildiz–Hassibi proof)   ← a full paper
   │
   ├─[C1] higher-order zero patterns
   ├─[C2] generalized GM-MDS (BDG24)  + linear field size   ← a full paper
   │
   └─[D1] generic RS are MDS(ℓ) ∀ℓ      (from B/C)
       └─[D2] generic RS list-decode to capacity (from A4 + D1)
            └─ specialize to UniversalGSListMassBound's list-size half (per-rate / large-q)
```

## 3. mathlib / ArkLib gaps (what does NOT exist today)

- No `MDS(ℓ)` / higher-order MDS definitions anywhere (only ordinary `IsMDS`).
- No generic-intersection-dimension theory.
- No GM-MDS theorem (Layer B) — neither statement nor proof.
- No generalized Singleton bound for list decoding / `LD-MDS` (Layer A3).
- No `MDS(L+1) ⟺ list-decodable` bridge (Layer A4).
- No genericity/avoid-subvariety machinery at the needed generality (Layer D).

Each bullet is, individually, substantial new theory. Layers B and C/D are each effectively a
research paper to formalize.

## 4. Effort and honest recommendation

This is a **multi-person-year** formalization frontier (it is an open target in the formalization
community for exactly this reason). The correct execution is a scoped, human-led project that
builds Layers A–D for **mathlib** (so the definitions get expert fidelity review), with an AI
assistant formalizing individual lemmas *after* the architecture and definitions are pinned down.
It cannot be single-shot, and it cannot be parallelized into existence by a subagent swarm —
attempting that yields `sorry`-stubs or unsound proofs (cf. issue #171). The honest near-term ArkLib
posture is unchanged: keep `UniversalGSListMassBound` and `FaithfulGSFamily` as named hypotheses;
the verified reduction *to* the MCA prize already routes through them.

## Sources

- [Generic Reed-Solomon Codes Achieve List-decoding Capacity (Brakensiek–Gopi–Makam, STOC 2023)](https://arxiv.org/abs/2206.05256)
- [Higher-Order MDS Codes (Roth)](https://arxiv.org/abs/2111.03210)
- [Generalized GM-MDS: Polynomial Codes Are Higher Order MDS (Brakensiek–Dhar–Gopi, STOC 2024)](https://arxiv.org/abs/2310.12888)
- [Improved Field Size Bounds for Higher Order MDS Codes](https://arxiv.org/abs/2212.11262)
- [AG Codes Achieve List-decoding Capacity over Constant-sized Fields](https://arxiv.org/abs/2310.12898)
- Ben-Sasson, Kopparty, Radhakrishnan, *Subspace polynomials and limits to list decoding of Reed–Solomon codes* (the worst-case impossibility, Layer 0).
- GM-MDS: Dau–Song–Dong–Yuen (conjecture); Lovett (2018); Yildiz–Hassibi (2018).

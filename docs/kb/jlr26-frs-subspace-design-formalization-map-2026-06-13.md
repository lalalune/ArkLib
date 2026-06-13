# JLR26/CZ25 — the FRS subspace-design proximity-gap solution, mapped to in-tree machinery

**Date:** 2026-06-13. **Source:** arXiv:2601.10047 (Jeronimo–Liu–Rajpal, "Optimal
Proximity Gap for Folded Reed–Solomon Codes via Subspace Designs", 15 Jan 2026; = CZ25 in
the in-tree naming), cross-checked against ABF26 (ePrint 2026/680). Both PDFs on disk at
`~/papers/arklib/`.

## 1. The result (complete, no open residual)

**JLR26 Theorem 5.12 / 6.2.** For an `m`-folded Reed–Solomon code `C = FRS^m_{n,k}` of rate
`R = k/(mn)`, every `η ∈ (0, 1−R)`, with `m ≥ c/η²` and `q` polynomially large in `n, 1/η`:
`C` has a line/affine proximity gap with target radius `δ* = 1 − R − η` and

```
ε ≤ (C₁/q)·(n/η + 1/η³),   κ = 1/n.
```

This is **exactly** the `mcaConjecture` form `ε ≤ (1/q)·n^{c₁}/η^{c₃}` with `c₁=1, c₃=3`.
A concurrent independent proof is Goyal–Guruswami (ECCC TR25-166 = ePrint 2025/2054), via
curve-decodability (vs JLR26's line-decodability).

## 2. The full proof chain → in-tree machinery status

| JLR26 lemma | statement | in-tree |
|---|---|---|
| Def 4.3 | τ-subspace-design code: `(1/n)∑ᵢ dim(Aᵢ) ≤ d·τ(r)` for `A≤C`, `dim A=d≤r`, `Aᵢ={a∈A:aᵢ=0}` | `CodingTheory.IsSubspaceDesign` ✓ [fleet] |
| Lemma 4.1 | Folded-Wronskian: `∑ₐ dim(U∩Hₐ) ≤ d(k−d)/(m−d+1)` | `gk16Claim16StructuralData_holds` ✓ [fleet] |
| Lemma 4.4 | FRS is τ-design, `τ(r) ≤ R + O(r/m) + O(1/n)` | (from 4.1) [fleet] |
| Lemma 5.4 | interpolation: `u(α)=∑αʲu⁽ʲ⁾`, deg-ℓ per coord, agree on `>ℓ` ⟹ agree on radius `δ/(1−ℓ/t)` | **`curve_agreement_card_le`** ✓ [this session, `CurveAgreementThreshold.lean`] |
| Lemma 5.5 | pruning: `Pin_ε(H)` distribution, `|S|≤d`, `H_S={0}`, pin prob `≥ε/(r+ε)` | `exists_separating_restriction_injective` + `subspaceDesign_random_coord_support_prob` ✓ [fleet] |
| Claim 5.8 | the δ-close codewords of a line lie in a common affine `H⊆C`, `dim H ≤ r` (rank-nullity + design) | **`subspaceDesign_list_dim_bound`** ✓ [this session, `SubspaceDesignListDim.lean`] |
| Lemma 5.7 | **line stitching**: τ-design ⟹ `(δ, a=r²t, t)`-line stitching | **OPEN** — combines 5.4+5.5+5.8 |
| Lemma 5.10 | line stitching + list-decoding ⟹ line correlated agreement, `ε=((t₂−1)L+a)/q` (peeling) | **OPEN** |
| Lemma 5.11/5.12 | assembly to the FRS bound | **OPEN** (mechanical from 5.10) |
| §6 | line proximity gap ⟹ affine proximity gap (averaging) | **OPEN** (combinatorial) |

So **two load-bearing ingredients (Claim 5.8 confinement, Lemma 5.4 interpolation) were built
this session**; the fleet's `IsSubspaceDesign`, Folded-Wronskian, and pruning (5.5) are already
in-tree. The remaining FRS gaps are **line stitching (5.7)** and **peeling (5.10)** — both fully
specified in JLR26 §5.3–5.4 with no open math.

The fleet audit (`docs/kb/audits/.../max-campaign-results.json`) had flagged the FRS list-decoding
core (ABF26 Cor 3.5 = CZ25 Thm B.5 = `subspaceDesign_list_decoding_cz25`) as "months of ground-up
formalization (mathlib has no subspace-design/FRS list-decoding API)". **That API now largely
exists.** Caveat: my `subspaceDesign_list_card_le` gives the *crude* `|F|^{r−1}` count
(confinement + cardinality), whereas the in-tree `CZ25DimensionCount` residual wants the *pruned*
poly bound `(1−τ(r₀))/η`; closing it needs the Lemma-5.5 pinning count on top of the confinement.

## 3. THE PRIZE BOUNDARY — plain RS ≠ FRS (this is the crux)

The ABF26 **grand MCA challenge** is for **plain RS** `C = RS[F,L,k]` over a *smooth* domain
(multiplicative subgroup, size a power of 2), constant rate `ρ ∈ {1/2,1/4,1/8,1/16}`, `ε*=2⁻¹²⁸`:
determine the largest `δ*_C` with `ε_mca(C, δ*_C) ≤ ε*`.

`FRS[F,L,k,1,ω] = RS[F,L,k]` is the **`s=1` (unfolded)** case. The JLR26/CZ25 route needs folding
`s = Ω(η⁻²)` (Lemma 4.4's `O(r/m)` term forces `m` large for `τ(r) ≈ R`). **So the subspace-design
route solves FRS (`s>1`), NOT the prize plain RS (`s=1`).**

This is confirmed by **ABF26 Table 1** (plain RS `ε_mca(C,δ)`):
- `δ < δ_min/2`: `ε_mca ≤ O(n)/|F|` [BCIKS20].
- `δ = J(δ_min) − η` (→ Johnson): `ε_mca ≤ n·poly(1/η)/|F|` [BCHKS25; Hab25; BCGM25; BCIKS20].
- `δ ≈ δ_min − Ω(1/log n)` (→ capacity): **`ε_mca ≥ n^{Ω(1)}/|F|`** [BCHKS25; KK25; CGHLL26].

So plain RS has a *near-capacity lower bound* — `δ*` is bounded away from capacity, and the
**window `(1−√ρ, 1−ρ−Θ(1/log n))` is genuinely open** for plain RS. The FRS positive result does
NOT transfer (the prize regime is exactly where the FRS technique fails).

## 4. The collapse / open frontier

The two grand challenges (MCA, interleaved list-decoding) **collapse to one iff the LD⇒MCA bridge
(ABF26 Thm 4.21)** holds for plain/interleaved RS — ABF26 states this is **open**. So the
genuinely actionable open routes for the *prize* (plain RS) are:
- (a) the LD⇒MCA bridge (4.21) for plain RS / `C^{≡m}`;
- (b) a plain-RS (s=1) beyond-Johnson list bound — but the near-capacity lower bound caps `δ*`;
- (c) pinning `δ*` exactly in the window via the line–ball incidence / character-sum face.

## 5. Other on-disk papers triaged (supporting, not prize-closing for plain RS)

- `arxiv-2510.13777` "From random to explicit via subspace designs" — the subspace-design
  transfer machinery (random↔explicit); FRS/AEL, not plain RS.
- `arxiv-2603.03841` "Advances in list decoding of polynomial codes" (Mar 2026) — survey of the
  FRS/multiplicity capacity line; no plain-RS window result.
- `arxiv-2511.05176` "Deterministic list decoding of RS" — algorithmic, Johnson-regime.
- `arxiv-2510.13775` "Combinatorial bounds for list recovery via Brascamp–Lieb" — list recovery,
  not the MCA window.

**Net:** the FRS subspace-design solution (JLR26/CZ25) is now ~70% formalizable from in-tree
machinery (Claim 5.8 + Lemma 5.4 landed this session; 5.7/5.10 are the remaining specified gaps).
The plain-RS prize is a *different, harder* object — open, capped near capacity, and only
reachable via the LD⇒MCA bridge or a new s=1 technique.

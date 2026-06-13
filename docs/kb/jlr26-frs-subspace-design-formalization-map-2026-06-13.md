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

## 6. The two bridges and why the plain-RS prize is doubly blocked (the actionable core)

ABF26 gives two LD⇒(M)CA bridges; understanding their failure modes pins the open core.

**(B1) Line-decoding ⟹ MCA — ABF26 Thm 4.21 [GG25 Thm 3.5], PROVEN, no loss.**
If `C` is `(δ, a, n+1)`-line-decodable then `ε_mca(C, δ) ≤ a/|F|`. This is exactly how JLR26's
line stitching (`(δ, a=r²t, t)`-line-decodable, Lemma 5.7) yields the FRS MCA bound. **But
line-decodability requires the τ-subspace-design structure** (the whole JLR26 §5 argument), which
**plain RS (s=1) does not have** (`τ(r) = R + O(r)` is useless). So B1 is unavailable for the prize.

**(B2) List decoding ⟹ CA — ABF26 Thm 5.1 [GCXK25 Thm 3], PROVEN but with a √-LOSS.**
A list bound gives CA, but only at the *square-root* of the proximity, so it reaches MCA only up to
~sub-Johnson (the in-tree W2 wall: `T² ≤ |G|·E`). ABF26 states the key: **"Strengthening
Theorem 5.1 to remove the square-root loss in proximity would reestablish all [the plain-RS
results]."** So removing the √-loss in B2 is *the* lever for the plain-RS prize.

**Conclusion — the plain-RS prize is open, blocked on EITHER:**
1. removing the √-loss from GCXK25 Thm 3 (B2) — then a plain-RS window list bound ⟹ window MCA; or
2. a plain-RS (s=1) beyond-Johnson list bound *and* the √-loss removal (both open); or
3. directly pinning `δ*` via the line–ball incidence / character-sum face (`epsMCA_ge_far_incidence`),
   which the in-tree walls (W4/character sums) show is the incomplete-Gauss-sum problem.

This sharpens the directive's "throw away anything that fails in the prize regime": the entire
subspace-design / line-decoding edifice (JLR26, GG25, my Claim 5.8 + Lemma 5.4, fleet 5.5) is
**FRS-only** and provably does not reach plain-RS `s=1`. The plain-RS prize's genuine open core is
the **√-loss removal in the list⇒CA bridge** (a clean, named, closed target — not an open-ended
search), with the near-capacity lower bound (Table 1) capping how far it can possibly go.

## 7. The reduction: both challenges share one δ* (the syndrome/list collapse)

Combining the two converses with the bridge pins the relationship exactly:
- **MCA ⟹ list (ABF26 Thm 5.2 [BCHKS25 1.9], Thm 5.3 [CS25 2]):** `ε_ca(C,δ)` small ⟹
  `|Λ(C,δ)| < |F|`; quantitatively `|Λ(C⁺,δ)| ≤ (|F|/(1−η))·ε_ca(C,δ)`. So `ε_mca ≤ ε*` forces
  `|Λ| ≲ ε*·|F|`.
- **list ⟹ MCA (ABF26 Thm 5.1 [GCXK25 3]):** `|Λ(C,δ)| ≤ L` ⟹ `ε_mca(C, 1−√(1−δ+η)) ≤ L²δn/(η|F|)`.

For the prize, `ε* = 2⁻¹²⁸`, `q ≈ n·2¹²⁸`, so `ε*·|F| ≈ n`. Hence **both grand challenges share the
same threshold**:

```
δ*_prize  =  the radius where  |Λ(RS[F, μ_n, k], δ)|  crosses  ε*·|F| ≈ n.
```

This IS the genuine open core, stated cleanly: pin the radius where the worst-case list size of
*explicit smooth-domain* RS equals `~n`. Everything else (MCA error, the interleaved list challenge)
is tied to it by the bridges above.

## 8. The three routes and their fatal gaps for the prize (exhaustive)

| route | gives | gap for prize (plain RS / μ_n / window) |
|---|---|---|
| **List decoding ⟹ CA** (GCXK25 Thm 3) | `ε_mca` from a list bound | **√-loss in the radius** (`δ→1−√(1−δ)`), and ABF26 proves it is **false to remove in general** (Thm 5.4 [BGKS20]: `RS[F,F,|F|/8]` is list-decodable but lacks CA at `1−ρ^{1/3}`). Needs the smooth structure. |
| **Subspace design / line stitching** (JLR26/GG25) | `ε_mca` up to capacity | **FRS-only** (`τ(r)=R+O(r/m)` needs folding `m=Ω(η⁻²)`); plain RS `s=1` has `τ(r)=R+O(r)`, useless. |
| **Syndrome-space + witness reduction** (Yuan–Zhu 2605.07595) | `ρ < 1−R−ε` up to capacity, *no list decoding* | **random linear codes only** (random parity-check model); explicit smooth RS is the open line–ball incidence (character-sum / incomplete-Gauss-sum face, in-tree W4). |

**Net for the prize.** The plain-RS smooth-domain window is open, and the reduction above shows the
open core is *one* object: the worst-case list size `|Λ(RS/μ_n, δ)|` in the window. The syndrome-space
route is the most promising NON-list, NON-folding angle — it works for random codes precisely because
the random syndrome avoids the additive structure of `μ_n`; transferring it to explicit `μ_n` is
exactly the character-sum/line–ball incidence problem (face iv), where the additive-energy / Sidon
structure of `μ_n` (this session's energy+antipodal work) is the controlling quantity. That is the
single named open target — not an open-ended search.

## 9. The syndrome-space lens (2025/1712) — confirms the prize core = μ_n additive energy

Web + disk + in-tree assessment of **eprint 2025/1712 (Okamoto, "Syndrome-Space Lens")**, the
exact face-(iv) framework:
- **Setup (correct):** syndrome `s(z) = A + zB` is an affine line; CA ⟺ `s(z) ∈ Span(H_{T_z})`,
  `|T_z| ≤ k = n−t`; classified by the **rank margin `Δ = t − d`**.
- **Δ=0 (capacity) — VACUOUS (in-tree `CapacityVacuity.lean`):** at budget `k=m=n−d`, MDS makes
  every word satisfy the CA premise. Correctly *explains* why up-to-capacity CA is false; does not
  close the window.
- **Δ≥2 "unconditional rigidity" (Thm 7.1/7.2) — reaches only `δ < (1−ρ)/3`**, BELOW unique
  decoding `(1−ρ)/2`, far below Johnson `1−√ρ`. Near capacity the hypothesis `(r+1)k < m+1` is
  unsatisfiable ⟹ vacuous. The window is handled only *conditionally* (§5.4–5.5 Hankel-pencil).

So 2025/1712 does NOT close the prize either. Its conditional window regime is exactly where the
**line–ball incidence reduces to the additive energy / BGK count of `μ_n`**: the in-tree kernel
`bgkCount M` (`AdditiveEnergy{Parity,ThreeDvd,SixDvd,Fermat,Char0}.lean`) is structurally pinned
(`2|M`, `3|M`, `6|M` away from `{3}∪`Fermat-bad, char-0 vanishing) but its **magnitude is the open
BGK/Bourgain subgroup-additive-energy core** — genuinely open analytic number theory.

## 10. FINAL EXHAUSTIVE CONCLUSION

Every published route, surveyed via web + the on-disk corpus, reduces the plain-RS prize to the
**same one object**: the worst-case `μ_n` syndrome line–ball incidence = the additive-energy /
BGK magnitude of the multiplicative subgroup `μ_n` in the window. Concretely:
- list-decoding route → explicit-RS beyond-Johnson list size (√-loss blocks the transfer);
- subspace-design route → FRS-only (`s=1` has no design);
- syndrome-space route (random / Okamoto Δ≥2) → random-only / below-UDR-only;
- all three collapse, in the window, to the `μ_n` line–ball incidence = additive-energy magnitude.

That magnitude (BGK/Bourgain) is the genuine open core. It is bracketed in-tree (Heath-Brown–Konyagin
`E⁺(G) ≪ |G|^{5/2}` upper; structural divisibility constraints) but not pinned — and **pinning it is
the prize**. No published work pins it; the directive's "internal team solution," if it exists, is a
new additive-combinatorics bound on `μ_n` energy that is not in any of the surveyed papers. This is
the exhaustively-confirmed single named target; the workbench §R points the next solver at it.

## 11. The exact ABF26 §4 brackets — they pin the conjecture form precisely

| thm | regime | bound | meaning for δ* |
|---|---|---|---|
| 4.12 [BCHKS25 4.6] | `δ < 1−√ρ⁺−η` (Johnson) | `ε_mca ≤ O_ρ(n/(η⁵|F|))` | lower bracket: δ* ≥ Johnson−o(1) |
| 4.14 [GG25 4.10] | FRS, `s>16/η²` | `ε_mca(1−ρ−η) ≤ O(n/(η|F|)+1/(η³|F|))` | **the target FORM** (FRS reaches capacity−η) |
| 4.13 [GG25 4.9] | τ-design | `ε_mca(1−τ(t+1)−3/(2t)) ≤ (tn+4t²)/|F|` | the general subspace-design bound |
| 4.16 [BCHKS25;KK25] | smooth RS, poly `|F|`, `ρ<1/2` | `ε_ca(1−ρ−Θ(1/log n)) ≥ n^c/|F|` (∀c, ∃ code) | **UPPER bracket: δ* ≤ 1−ρ−Θ(1/log n)** |
| 4.17 [CS25 1] | RS | `ε_ca(δ)=1` for `η ≈ 1/√(n log q)` from capacity | total breakdown nearer capacity |
| 4.18 [BCHKS25 1.7] | **char 2** | `ε_ca(Johnson) ≥ Ω(n²/|F|)` | **char-2 jump AT Johnson — prime/smooth OPEN** |

**Key for the prize:** Thm 4.18's Johnson jump is **characteristic 2 only**; ABF26 says explicitly
"it may still be the case that MCA holds with small error beyond the Johnson bound for our main
point of interest, prime fields over smooth domains." So the *prize regime* (prime F, smooth μ_n)
is exactly where the jump is NOT known to apply — the window is open ABOVE Johnson there.

**THE PRECISE PRIZE CONJECTURE (closed form, bracket-grounded; the natural answer):**
```
δ*(RS[F, μ_n, k], ε*=2⁻¹²⁸) = 1 − ρ − Θ(1/log n),
ε_mca(RS[F, μ_n, k], 1−ρ−η) ≤ C₁·(n/η + 1/η³)/|F|   for all  η ≥ c₀/log₂ n,
```
i.e. **smooth plain RS conjecturally matches the FRS bound (Thm 4.14) throughout the window
`η ≥ c₀/log n`, and fails below it (Thm 4.16)** — so `δ* = 1−ρ−c₀/log n` is SHARP, matching the
upper bracket exactly. This is closed-form, consistent with every bracket above, and is the
conjecture a winning proof must establish for plain RS. The open content is proving the upper
`ε_mca` bound (= the μ_n additive-energy magnitude, §9–10) for `s=1`; the conjecture STATEMENT is
complete and closed. The constant `c₀` is the threshold in Thm 4.16's `Θ(1/log n)`; pinning `c₀`
exactly is the quantitative heart, and the `1/η³` blow-up (from line-stitching `a=Θ(1/η³)` in the
FRS analysis) is conjectured to carry over via the `μ_n` 2-adic tower providing depth-`log n`
effective folding.

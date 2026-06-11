# Pinning δ\* — Fable's attack dossier (issue #357)

> Working research log. The honesty contract of #357 applies: open core stays a named
> surface, every attempt lands in `DISPROOF_LOG.md` with a constraint lemma, probes precede
> Lean. This file is the *intellectual* plan (the 9 hypotheses + 3 connections + ranking);
> the bricks land in `ProximityGap/` and `Frontier/`.

## 0. The problem, restated for an attacker

`C = RS[F, H, k]`, `H ≤ F^×` a multiplicative subgroup, `|H| = n = 2^μ`, rate `ρ = k/n`,
`|F| < 2^256`, `ε* = 2^-128`. `ε_mca(C,δ)` = max over lines of the bad-point fraction, where a
point `g` is *bad* if some witness set `S` (|S| ≥ (1−δ)n, a codeword agrees with g on S) does
**not** witness the whole line. `δ*(C,ε*) = sup{δ : ε_mca(C,δ) ≤ ε*}`. We must produce a `δ₀`
with `ε_mca ≤ ε*` for `δ ≤ δ₀` (a `le_mcaDeltaStar_of_good` instance) **and** `ε_mca > ε*` for
`δ > δ₀` (a `mcaDeltaStar_le_of_bad` instance) that **meet**.

## 1. Why it is hard — the honest difficulty

Two walls, and they are the *same* wall:

1. **Floor↑ ⟺ beyond-Johnson explicit-RS list decoding (25-yr open).** Pushing `ε_mca ≤ ε*`
   above the Johnson radius `1−√ρ` requires bounding the interleaved list size of an *explicit,
   fixed, smooth* RS code past Johnson. No technique does this; Johnson is the list-decoding
   wall for explicit RS, and the random-RS capacity results (GZ23, GG25, CZ25) are ensemble-only
   with no derandomization.
2. **Ceiling↓ ⟺ the same.** Pushing `ε_mca > ε*` *down* toward Johnson means exhibiting bad
   families just past Johnson — but the KKH26 construction (the only known one) lives near
   capacity (`1−ρ−(2m−1)/n`, the gap identity), and CS25/BCHKS25 *couple* any improvement to the
   list-decoding question. So both directions terminate at the same 25-year obstruction.

The bracket is `[1−√ρ , 1−ρ−(2m−1)/n]` and **nothing census-aware lives between them**. Every
in-tree bound is *census-blind*: it sees MDS distance data (M1, M2) but not the evaluation-domain
structure. Yet the random-RS results prove δ\*(smooth) and δ\*(random) **must differ** — so the
gap is precisely where a domain-separating mechanism must act. The probe campaign found exactly
one: **M3 / the Möbius-involution pencil energy `E₂(H) = Σ_φ t₂(φ)²`** separates smooth subgroups
(`E₂ ≈ n²·c`) from random domains (`E₂` thin). *This is the only handle on the gap.*

## 2. Latest research state (June 2026, swept end-to-end)

No edge-movers beyond the held table exist. Floor held to Johnson by full MCA (BCGM25/Hab25/
BCHKS25). Ceiling held near capacity (KKH26, Kambiré). At-capacity conjectures FALSE (CS25/KK25/
DG25, three groups). Protocol-level results (Chai–Fan 858/861) *sidestep* `ε_mca`. The window is
untouched. The in-tree new math that *moves* it: the Parseval exponent-halving (opens s=64
unconditionally), the stratified-spread ceiling (reaches below δ=1/2), the DEEP-quotient transfer
(LD↓ ⟹ MCA↓ generically), interleaving exactness (one ledger for MCA + interleaved LD), and the
M3 domain separation (the only census-aware fact).

## 3. The most promising open direction, and the broad idea nobody has implemented

**The unification bet, sharpened by the census.** Every known counterexample family — CS25, KK25,
prime-field, KKH26 — lives on **coset/orbit structure**. The natural conjecture (untried; no one
has imported additive-combinatorial inverse theory here): *any ε\*-bad line family in the window
over a smooth domain is `poly(1/ε)`-covered by affine-/multiplicative-subgroup-structured
families.* If true, the upper bracket becomes **enumerable**: δ\* = the largest δ at which no
structured bad family of size > ε\*·q exists, computable from the structured catalogue.

What is new: the bridge from Bogolyubov–Ruzsa/Sanders (quantitative inverse sumset theory) to the
agreement census, **via the Möbius-pencil energy as the Fourier-side first invariant.** Why nobody
has done it: the proximity-gaps literature works above the pair level (second moments) and is
census-blind; the inverse-sumset literature has never met evaluation-domain RS. The probe-verified
M3 separation is the empirical anchor that says "the structured families are the only shape" is not
hopeless. Likely refutation: the inverse theorem's loss factors (`exp(poly log(1/ε))` in Sanders)
may be too lossy to pin a *point* (only a band). Not obvious because the smooth-domain pencils are
*highly* structured (subgroup orbits, not generic), so the inverse theorem could be lossless here.

## 4. The 9 hypotheses

### Reasonable (existing math, used insightfully)

**R1 — δ\* = Johnson for the MCA functional specifically (MCA is strictly harder than LD).**
The empirical transition sits *on* Johnson at large field. Conjecture: `ε_mca(C, 1−√ρ+η) > ε*` for
every `η>0` at deployed params, driven by the *mutual* requirement (every witness witnesses the
line), which the in-tree witness-spread engine lower-bounds and which activates past Johnson even
where the code is still list-decodable. Novel angle: run `DeepQuotientTransfer` in reverse —
MCA-specific witness-spread fails where LD succeeds. *Refutation:* if witness-spread is itself
Johnson-capped (like 2nd moments), R1 dies. Interesting: would make δ\* = the floor, *decoupling*
the prize from the 25-yr wall.

**R2 — the KKH26 ceiling is tight: δ\* = 1−ρ−(2m−1)/n in the high-degree regime.** The gap
identity pins the ceiling exactly. Conjecture: the matching lower bound holds because the
stratified-spread count is the *maximum* bad-scalar count (a menu-law upper bound on bad scalars).
Novel angle: prove `kkh26_stratified_count` is extremal via the incidence menu law `C(m₀,s/4−|J|)`.
*Refutation:* a non-KKH26 bad family below the ceiling. Interesting: pins δ\* at the *ceiling* edge.

**R3 — bracket interpolation via the LD⇔MCA dictionary.** `ε_mca ≈ |Λ(C^{≡m},δ)|/q` (in-tree).
Force the interleaved list size, as a function of δ, to cross `ε*·q` at a unique point via
monotonicity + the GS list-size derivative. *Refutation:* integer jumps kill IVT (a band, not a
point) — unless the *average* list size is smooth. Interesting: well-posed in-tree, cheap to test.

### Novel (brand-new math)

**N1 — the Möbius-energy law: δ\*(H) = F(E₂(H)/n²).** Build a δ\*-formula in the pencil energy
`E₂(H) = Σ_φ t₂(φ)²`, `F` interpolating Johnson (E₂ thin) to a smooth value (E₂ ≈ n²/4). Mechanism:
bad lines past Johnson force high-agreement codeword pairs, which over a subgroup are pinned onto
Möbius-involution orbits (`σ(x) = −b/x : H→H`), and the bad-scalar count is governed by `E₂`. *The
only domain-separating mechanism.* *Refutation:* `E₂` controls only M3 (low moments); δ\* may need
the sup over received words (high moments). Not obvious: the separation is REAL and must factor
through *something* census-like — `E₂` is the unique candidate.

**N2 — lacunary cyclotomic-resultant structure theorem.** A structural upper bound on
`|Res(R, Φ_{2^m})|` for *sparse* ±1 collision differences `R`, beyond Parseval, via the
rotation-orbit reduction — opening s=128 without Thorner–Zaman. Mechanism: few nonzero coeffs force
lacunary cancellation in the cyclotomic norm. *Refutation:* a sparse worst case saturating Parseval.
Not obvious: probes show ℓ²-mean conjugate behaviour (room below worst case).

**N3 — the witness-rigidity decoupling (the holy grail).** A new functional `Rig(C,δ)` = the
minimum witness-set variation over bad configs, with `ε_mca ≥ g(Rig)` where `g` activates past
Johnson *even when LD succeeds*. This severs MCA from the LD wall. Mechanism: "every witness
witnesses the line" is a rigidity that fails generically past Johnson. *Refutation:* rigidity may be
implied by list-decodability. Not obvious: MCA ⪈ CA ⪈ PG, and the gaps can activate at different δ.

### Synthetic (interpolating in-tree engines into new insight)

**S1 — the transfer fixpoint.** Compose `DeepQuotientTransfer` (LD↓⟹MCA↓) with interleaving
exactness (brackets transfer verbatim) into a self-consistency `δ\* = T(δ\*)`; solve the fixpoint.
*Refutation:* the "up to explicit factors" loss makes it a band.

**S2 — the exact bad-scalar census.** `Parseval ⊗ stratified-spread ⊗ menu-law` → the bad-scalar
count is *exactly* the menu-law sum, pinning the ceiling with matching upper+lower on the count.
*Refutation:* the menu law is probe-verified only to s=64; char-0→mod-p lifting fails at n=64.

**S3 — the gap identity is the pencil-energy deficit.** Conjecture `(2m−1)/n = (E₂-deficit of the
bad line)/n²`, unifying the ceiling with the M3 invariant. *Refutation:* the gap identity is a
degree/dimension count, plausibly pencil-independent.

## 5. The 3 paperworthy connections (unifications/symmetries)

- **C1 — Agreement census ⟷ Möbius orbits ⟷ δ\* domain separation.** The smooth/random δ\*
  distinction factors through the pencil energy `E₂`; M3 is the first moment-level smooth/random
  invariant, with the Möbius involution `σ(x)=−b/x` as the mechanism. (Foundation for N1, S3.)
- **C2 — DeepQuotientTransfer ⟷ interleaving exactness ⟷ one ledger.** MCA and interleaved RS
  list-decoding are *the same problem* in-tree: the transfer functor + exactness collapse two
  trackers into one bracket. (Foundation for S1, R3.)
- **C3 — Parseval halving ⟷ ℓ²-vs-ℓ¹ conjugates ⟷ resultant-as-Fourier-energy.** The KKH26 prime
  threshold is a Parseval bound: the bad-scalar distinctness exponent is the cyclotomic Fourier
  energy of collision differences. (Foundation for N2, S2.)

## 6. Ranking and execution order

**Ease (cheapest to prove/refute first → hardest):**
A5-exact-point · M3-H4-reduction · M3-H2-(k=2-domain-indep) · R3 · S2 · R2 · N2 · S1 · R1 · N1 · N3.

**Promise (most likely to actually pin δ\* → least):**
N1 · N3 · (unification-bet) · S1 · R1 · S3 · R2 · S2 · R3 · N2 · A5.

**Combined-score start order (work ALL, brick by brick):**
1. **Foundation first** (high ease, enables the promising ones): the **M3 reduction (H4) + k=2
   domain-independence (H2)** formalized, and the **A5 first-exact-δ\*-point** (validates the engine
   end-to-end; a genuine first — no exact δ\* exists for any code anywhere). These are concrete and
   build the census substrate N1/S3 need.
2. **Then the promising core:** push **N1 (Möbius-energy law)** on the census foundation, with **S3
   (gap = energy deficit)** as its falsifiable corollary, mutually-falsified against **R2**.
3. **In parallel, cheap kills:** **R3** (interpolation — quick IVT check) and **S2** (menu-law
   census — probe past s=64).

Every refutation is a constraint lemma in `DISPROOF_LOG.md`. Survivors get red-teamed and promoted.
If all 9 die, regenerate 3+3+3 and continue. **Start: the M3 reduction + A5 exact point.**

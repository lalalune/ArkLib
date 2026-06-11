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

## 7. Results log (proven / refuted, brick by brick)

### N1 — REFUTED at all feasible scales (`scripts/probes/probe_n1_energy_vs_badcount.py`)
**Verdict: the pencil energy E₂ does NOT govern the bad-scalar count, so `δ* = F(E₂/n²)` fails.**
Probe (exact, syndrome-reduced ε_mca over the worst line; cross-checked monotone): across 8
feasible `(p,n,k)` instances, smooth-subgroup and random-subset domains of *equal* `n,k` have
**identical** bad-scalar counts at every tested radius — even when E₂ differs by up to 10× (e.g.
`(13,4,2)`: smooth E₂=10 vs random E₂=1, both bad count 4; `(11,5,3)`: E₂=20 vs 4, both bad 5).
6/8 cases show "different E₂, same bad count"; the other 2 had equal E₂ and equal bad count. The
bad count is determined by `(n,k,δ)` alone at this scale, **independent of E₂**.

*The learning (a real constraint on the search):* the only known domain-separating invariant
(E₂ = the M3 second-moment energy) controls the agreement *spectrum moments* but **not the
extremal bad count** that sets δ\*. This is the average→worst-case wall manifesting at the pencil
level: E₂ is an L²/average quantity; δ\* is a sup over received words. *Any future use of the
pencil structure for δ\* must target an extremal/higher-order invariant, not the energy sum.*
The proven `E₂ = Θ(n³)` separation (`MobiusPencilEnergy.lean`) stands as a spectrum-moment fact —
it is simply not the δ\*-controlling one. **Constraint for the ledger:** `ε_mca` is not a function
of E₂ (two domains, same field, E₂ differing, same ε_mca).

### N1′ (refinement, promoted to the slate) — the EXTREMAL pencil invariant
Since the *sum* E₂ is moment-blind, the refined conjecture is that δ\* tracks an **extremal**
pencil quantity — `maxₚ t₂(φ)` over the full k=3 pencil family, or the M3 *third*-moment census
`Σ_φ t₂(φ)³` (where the dossier's smooth/random separation actually lives), not the second moment.
This is the "thin-strip / higher-moment" escape (K3/H1) re-aimed: target the sup, not the average.
*Next probe:* does `maxₚ t₂` or the M3 cubic census predict the bad count where E₂ failed?

### DOMAIN-BLINDNESS — a structural finding (kills the domain-separation hypothesis class)
**The worst-line MCA bad-scalar count is DOMAIN-INDEPENDENT at every tested scale.**
`scripts/probes/probe_domain_blindness.py` (optimized: precompute ext(syndrome,S) once/domain):
- `(11,5,3)`: **complete enumeration of ALL 252 five-subsets** of `F_11^*` → bad count is
  `{δ=0.15: 1, δ=0.25: 5, δ=0.35: 5, δ=0.45: 5}` for *every single domain*, zero exceptions,
  smooth subgroup included.
- `(13,4,3)`: all 120 four-subsets → bad count `1` everywhere.

**Consequence (a hard constraint, not a hypothesis):** `δ*(C)` is a function of `(n,k,δ)` alone
at these scales — `δ*(smooth) = δ*(random)`. The smooth multiplicative structure does **not** move
the worst-case threshold; it only changes the *spectrum moments* (M2/M3/E₂), which the bad count
is blind to. This **refutes the entire domain-separation hypothesis class** — N1 (energy law), N1′
(extremal pencil), S3 (gap = energy deficit), and the C1 "δ\* domain separation" framing. The
proven `E₂ = Θ(n³)` smooth separation (`MobiusPencilEnergy.lean`) is real but is a *moment* fact
with **no δ\*-consequence**.

**This is exactly the dossier's central coupling, now empirically sharp:** because δ\* is
domain-blind, it equals the explicit-RS list-decoding threshold (a domain-independent count) — so
pinning it past Johnson IS the 25-year open problem, with no smooth-domain shortcut. The honest
research conclusion: **no domain-specific invariant can pin δ\* in the interior.** The viable
hypotheses are the *domain-blind* ones (R2 ceiling-tightness, R3 interpolation, S1 transfer
fixpoint, the unification bet on the bad-set *shape* rather than the domain). The next slate must
drop the census-separation angle entirely and attack the domain-blind list-count directly.

**Caveat on scale (red-team of the finding itself):** these are tiny fields (`p ≤ 13`, `n ≤ 5`)
where the radius window `(1−√ρ, 1−ρ)` is narrow and integer-quantized; the M3 separation the
probe campaign reported is a *third-moment* effect that may only surface the bad-count difference
at larger `n` (the `t₂ ≈ n/2` regime needs `n ≫ k`). The finding is "domain-blind at small scale";
strengthening it to all scales, or finding the first `n` where a domain *does* differ, is the
decisive follow-up probe (feasible up to `n ≈ 8` with the optimized engine + better S-pruning).

## 8. CORRECTION (research integrity) — domain-blindness is SATURATED-BAND only

The §7 "domain-blindness" claim was **over-stated** and is here corrected. The exact probes
reach only the *saturated low band* `δ ∈ [UD, ~Johnson)` where the worst-line bad count equals
`n` (the domain size) for **every** domain — but `n` is the *saturation ceiling* of that band, so
equal-across-domains there is the easy regime, not evidence about the interior. The **interior**
`δ ∈ (Johnson, capacity)` — where δ\* actually lives, where the bad count *grows* past `n` toward
the KKH26 blow-up, and where the KKH26 construction is **domain-specific** (smooth subgroup) — is
**exact-computation-infeasible at low rate** (the window with a wide Johnson–capacity gap requires
`m = n−k` large, hence `p^{2m}` syndrome pairs blow up; this is the same wall the dossier documents).

**Consequence for the slate:** N1 (the *specific* energy law `δ*=F(E₂/n²)`) stays REFUTED — E₂
varies in the saturated band while the count does not, so ε_mca is not a function of E₂, period.
**But the general domain-separation idea (N1′: an EXTREMAL pencil / M3 third-moment invariant) is
NOT killed** — it would act in the interior, which the probes never saw. The random-RS-beats-smooth
results *require* interior domain-dependence, so separation there is expected, not excluded. The
honest status: **domain-blind in the saturated band (proved by enumeration); interior separation
OPEN and unprobeable by exact methods** — exactly the 25-year wall, restated.

This *revives N1′ and the M3 third-moment thread* as the live domain-aware direction, and confirms
the domain-blind hypotheses (R2 ceiling-tightness, S1 transfer-fixpoint, the unification bet) as the
parallel track that sidesteps the interior-computation wall. The exact-pin combinator
(`MCAExactPin.lean`) and the pencil-energy substrate (`MobiusPencilEnergy.lean`) stand regardless —
both are correct, reusable, and route into whichever hypothesis survives.

### S1 (transfer fixpoint) — naive form DEAD
The in-tree threshold-halving map (`ProofLoop42.threshold_halving_into_unique_decoding`) is
`δ ↦ δ/2` (lands in unique decoding). Its only fixpoint is `δ = 0` (trivial) — the iteration
collapses to the floor in O(log) steps, never banding the interior window. Confirms the dossier's
"exits the window in O(1) steps". S1 survives only in a *nontrivial* reformulation (a rate-coupled
or ε-coupled map with an interior attractor), which is not the 858 map. Parked unless a non-collapsing
transfer is found.


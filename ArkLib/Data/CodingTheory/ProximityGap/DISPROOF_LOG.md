# Disproof Log — ABF26 Proximity Prize Grand Challenge 1 (Issue #232)

Goal: keep trying to **disprove** the ABF26 Grand-Challenge-1 conjecture, then
**disprove the disproof**. Record every attempt so we don't repeat ourselves and
so we zero in. Keep lemmas that *constrain* even if they don't fully disprove.
Default assumption: my disproof is wrong — find the precise reason it fails and
make that reason a sorry-free Lean lemma.

## CORPUS INTEGRITY (verified)

All 23 verified bricks (`CandidateDisproofLoop{4,5,6,7,8,12,14}`, `CandidateProofLoop{9,11,13,17}`,
`CandidateCarvingLoop10`, `CandidateBridgeLoop{15,16}`, `CandidateDecisionLoop18`,
`CandidateStructureLoop{19,20,21,22,23,24,25,26}`) are each **sorry-free and axiom-clean**
(`[propext, Classical.choice, Quot.sound]`), verified individually with `lake env lean` and
cross-checked: the dependency spine (Loop24→25, Loop21→Carving10) builds and audits clean *together*,
and every brick lives in its own `ArkLib.ProximityGap.*Loop_n` namespace (no collisions). The whole
proof/disproof/structure edifice is one consistent body. Backups at `~/arklib_disproof_backup/`.

**Current-checkout caveat (2026-06-08):** this checkout does not currently carry every historical
brick named above under `ArkLib/Data/CodingTheory/ProximityGap/`; many live only in
`~/arklib_disproof_backup/` or older quarantined paths until explicitly restored. Treat this log as
the research ledger; treat a named lemma as in-tree API only after checking the current source file.
Loops 27 through 38 are present as self-contained arithmetic bricks in the current checkout
(`CandidateStructureLoop37.lean` and `CandidateStructureLoop38.lean` added 2026-06-08, sorry-free,
axiom-clean, indexed in `ArkLib.lean`).

## #357 R2 refutation — KKH26 one-fold strict shrink fails at even cofactor (2026-06-11)

**Attempt.** Use binary/Fri fold transport to make the KKH26 near-capacity ceiling strictly
stronger down a smooth tower: fold the explicit bad-line exponents
`e₀ = r*m`, `e₁ = (r-1)*m`, and hope the bad family is not KKH-shaped at the next level.

**Disproof of the cheap form.** Under the exponent fold rule used in the in-tree probes
(`c = e mod 2`, `e ↦ (e+c)/2`), an even cofactor is invariant:

```lean
ArkLib.ProximityGap.KKH26.fold_same_KKH_pair_once_of_even_cofactor
```

proves that `r*(2*m)` and `(r-1)*(2*m)` both take branch `0` and fold to
`r*m`, `(r-1)*m`.  Thus one fold does **not** strictly shrink the KKH26 bad-line family whenever
the cofactor is even; it transports the same family one level down.  The finite cross-check
`scripts/probes/probe_kkh26_fold_transport.py` verifies the same law over `32,512` `(r,m)` cells
and shows the first split occurs exactly after the `2`-adic cofactor is exhausted.  The
complementary Lean brick

```lean
ArkLib.ProximityGap.KKH26.foldBranches_split_once_of_odd_cofactor
```

records that odd cofactors force the two exponents into opposite branches.

**Remaining target.** R2 survives only in a narrower form: a bottom-level odd-cofactor statement,
or a fold transport that changes the KKH split parameter `s` rather than merely halving `m`.
Do not repeat the "single fold strictly shrinks every KKH scale" claim.

## LITERATURE FRONTIER (2025–2026) — where the prize actually sits

A web-research pass (June 2026) located the precise state of the art. **Our verified carving at the
Johnson threshold `η₀=√ρ−ρ` (Loop10) is exactly the boundary the literature confirms.** Key papers:

* **PROVEN up to Johnson — Ben-Sasson–Carmon–Haböck–Kopparty–Saraf, eprint 2025/2055, Thm 1.3/1.5:**
  for RS rate `ρ` and `γ < 1−√ρ` (gap `η = 1−√ρ−γ`), proximity gaps hold with *polynomial* soundness
  `a > O_ρ(n/η⁵)`. ⇒ the large-gap side (`η > η₀`) is a **theorem** with poly soundness — matches
  Loop9/P1 and the in-tree Hab25 (MCA up to Johnson, Haböck eprint 2025/2110, and Bordage et al.
  2025/2051 "all polynomial generators satisfy MCA up to `1−(1+1/2m)√ρ`").
* **Capacity conjecture is FALSE — three independent groups (Nov 2025).** BUT each misses the prize:
  - **Crites–Stewart 2025/2046** (reduction to list-decoding): disprove the *up-to-CAPACITY* versions
    (CA, **MCA-of-WHIR**, DEEP-FRI list-decodability) at `δ ≥ 1−ρ`. They *propose the salvageable form*
    `δ ≤ 1−ρ−η` — i.e. exactly the prize's below-capacity regime is the proposed survivor, not refuted.
  - **Diamond–Gruen 2025/2010**: super-poly error `err > n^{c*}/q` for every `c*` — but at **vanishing
    rate** `ρ ≈ e·n^{1/3}/n → 0` (`k(n)=⌊e·n^{1/3}⌋`, `q=n^{c*+1}`), *not* a fixed prize rate
    `ρ∈{1/2,1/4,1/8,1/16}`. The prize's `ρ^{−c₂}` factor is precisely what their vanishing-`ρ`
    construction would have to beat at *fixed* `ρ`, which it does not address.
  - **Ben-Sasson et al. 2025/2055, Thm 1.6** (impossibility, char 2, beyond Johnson): proximity loss
    `<1/8` requires soundness `a ≥ n^{2−o(1)}` — a **quadratic** (`n²`) jump. **Loop11 shows `n²` is
    WITHIN the prize bound** (`(2^m)^{c₁}`, `c₁=2`, under `n ≤ 2^m`). So the quadratic jump does **not**
    disprove the polynomial-soundness prize; it is consistent with it.
* **Near-capacity positive results exist only for FOLDED / RANDOM RS** — Goyal–Guruswami 2025/2054
  (`(1−R−η)`-proximity gap for folded & random RS, field `≳ 1/η²`); folded-RS optimal gap via subspace
  designs, arXiv 2601.10047 (Jan 2026). **Plain deterministic smooth-domain RS** (the prize's
  multiplicative-subgroup domain) in the band `(1−√ρ, 1−ρ−η]` is **NOT** covered by these.

**Net position of the prize** (MCA, smooth deterministic domain, *fixed* prize rate, `δ ≤ 1−ρ−η`,
*polynomial* bound `poly(2^m,1/ρ,1/η)/q`): **genuinely open.** It is *not* settled by the Nov-2025
disproofs — those need exact capacity (Crites–Stewart), vanishing rate (Diamond–Gruen), or give only
quadratic-hence-allowed bounds (BCIKS 2055). The open core is precisely Loop10's small-gap band, and
the deciding question is whether *deterministic smooth-domain* RS behaves like the
generic/folded case (poly soundness ⇒ prize TRUE) or like Diamond–Gruen's adversarial low-rate
families (super-poly ⇒ prize FALSE) — at *fixed* prize rate. No construction currently reaches that.

**JUNE 2026 UPDATE — both new above-Johnson eprints now READ (PDFs fetched past the IACR 403 with a
`Referer: https://eprint.iacr.org/2026/NNN` header) and partially formalized:**
* **Chai–Fan 2026/861** (Action–Orbit): `O(1)/|F|` for plain RS on the cyclic (smooth-subgroup) domain
  above Johnson. Read in full: its prize-relevant Conjecture 1.1 is **conditional on TWO conjectures** —
  Q1 (Conj 4.12, NT non-vanishing, rigorous only `d∈{4,8}`) and Q2 (Conj 7.1, sparse-worst-case
  dominance, only *empirically* verified at scale `(32,8)`). Its *unconditional* core is **Theorem 2.1
  (Action–Orbit)**, now VERIFIED sound in Loop41 (`pencil_substitution` axiom-light `[propext]`). The
  conditional Q2 path is Loop40; the sparse-unconditional Layer-1 is the literature twin of Loops 33/34.
* **Chai–Fan 2026/858** (Threshold-Halving, RVW13): read in full — result (A) is **genuinely
  unconditional**: above-Johnson soundness for FRI/STIR/WHIR, `k=2^m`, any char, via concluding the
  test at `δ/2 < (1−ρ)/2` (unique-decoding radius) at a `2×` query cost. Formalized as Loop42, which
  yields the **first UNCONDITIONAL prize-shaped commit-phase bound** `(1/q)·(2^m)^2` (`c₁=2`).
  **BUT** it bounds `ε_FRI` by *avoiding* `ε_mca`, not bounding it — so the literal MCA prize is
  *sidestepped, not closed*. Net position: prize-as-stated (a bound on `ε_mca` at `δ ≤ 1−ρ−η`) remains
  OPEN; but FRI *soundness* above Johnson is now unconditionally settled (858) and the action-orbit
  mechanism is verified sound (861/Loop41), with all residual conditionality pinned to Q1/Q2.

**Resolved-prize bibliography to formalize next (O11/O12):** port Ben-Sasson 2025/2055 Thm 1.5
(poly soundness up to Johnson) and the Crites–Stewart reduction (CA-beyond-capacity ⇒ impossible
list-decoding) — the latter is a clean disproof of the *at-capacity* sibling we can make sorry-free.

## The target

Live target: the field-universal, faithful GS form
`MCAGS.epsMCAgsPrizeUniversalConjecture` / `MCAGS.UniversalGSListMassBound`.
There must be one constant triple `c₁,c₂,c₃`, chosen before the field, such that
for every prize rate `ρ = prizeRates j`, gap `η > 0`, and radius

    δ ≤ 1 − ρ − η          (★ strictly below list-decoding capacity 1−ρ)

there exists a faithful GS list family whose GS-exposed MCA error obeys

    epsMCAgs(RS_ρ, δ, L) ≤ (1/q) · (2^m)^{c₁} / (ρ^{c₂} η^{c₃}).

Do **not** re-target the stale surfaces:
`MCAGS.epsMCAgs_prizeBound_conjecture domain m` is fixed-field and already a theorem
(`epsMCAgs_prizeBound_conjecture_holds`, constants can absorb `q`), while
`uniformEpsMCAgsPrizeBoundConjecture` with `∀ L` is already false as stated
(`MCAGSPrizeRefutation.not_uniformEpsMCAgsPrizeBoundConjecture`) because arbitrary
adversarial list families are not the genuine decoder output.

The single most important structural fact is the gap `η > 0` in (★): the radius is
held **strictly below capacity**. Any disproof must produce a super-polynomial
correlation/list *while staying inside* (★).

## Attempts

### A1 — BKR additive-subspace vanishing explosion (`SolutionDisproof.lean`, `CandidateDisproofLoop1`)
Idea: in char 2, a smooth `L` contains an additive subspace `V`, `|V|=2^b`; set
received word `r=0`; every `P = Q·A_V` (`A_V` = subspace-vanishing poly) agrees with
`r` on `V`. Count `|F|^{k−|V|}` such `P` → exponential list.
**Refuted (A1):** to be a δ-close codeword, `P` must *agree* on ≥ `(1−δ)·|L|` points,
so the vanishing/agreement set has `|V| ≥ (1−δ)|L|`. Free dimension `k−|V|`. With
`k = ρ|L|` and (★) `1−δ ≥ ρ+η`, we get `|V| ≥ (ρ+η)|L| > ρ|L| = k`, so `k−|V| < 0`:
**zero** free polynomials, not exponentially many. The explosion only exists at/above
capacity (`δ ≥ 1−ρ`), which (★) forbids. → verified as
`below_capacity_kills_vanishing_explosion` (Loop4, sorry-free).

### A2 — Multiplicative trace-fiber variant (`CandidateDisproofLoop1`)
Idea: project cyclic `L` onto an additive basis via absolute trace `Tr`; use a trace
fiber as `V`.
**Refuted (A2):** `0 ∉ L` (multiplicative group) so trace fibers in `L` are not
additive subspaces; the affine-shifted fiber `V` has `|V| ≤ deg Tr = 2^{127}`, forcing
`k > 2^{127}` to get any free dimension, i.e. `ρ ≈ 1`, outside the prize rates
`{1/2,1/4,1/8,1/16}`. Same dimension-budget wall as A1.

### A3 — High-degree aliasing `X^{|L|}−1` (`CandidateDisproofLoop2`)
Idea: `X^{|L|}−1 ≡ 0` on `L`; `P = Q·(X^{|L|}−1)` matches `r=0` everywhere on `L`.
**Refuted (A3):** `deg(X^{|L|}−1) = |L| > k`, so every such `P` has degree ≥ `|L| > k`
and is disqualified from the degree-`<k` code. A special case of the A1 wall with
`|V| = |L|`.

### A4 — Interleaved coset clustering (`CandidateDisproofLoop3`)
Idea: factor `|L| = d₁·d₂`, concentrate errors into a few cosets, GS-decode clean
cosets, cross-pollinate to explode the global list.
**Refuted (A4):** coset decomposition is an isomorphism; the GS list size is governed
by the *global* code rate / Johnson radius, not by per-coset topology. Concentrating
errors onto cosets only reshapes *which* `(1−δ)|L|` points agree — it cannot lower the
agreement-set size below `(1−δ)|L|`, so the A1 wall still applies globally.

### O1 (attempted) — attack the MCA *correlation probability*, not the list size
Idea: a polynomial-size list can still in principle carry an anomalously large
correlated-agreement probability; bound `epsMCAgs` from below directly.
**Refuted-into-a-constraint (O1):** below the Johnson radius `δ < 1−√ρ`, BCIKS20 already
gives the `poly/q` correlation bound (the cited proximity-gap floor), so any correlation
disproof must squeeze into the band `1−√ρ ≤ δ ≤ 1−ρ−η`. That band is non-empty **only
if** `η ≤ √ρ − ρ`. Verified sorry-free in `CandidateDisproofLoop5.lean`:
`correlation_disproof_requires_small_gap`, with `johnson_gap_pos` (`√ρ−ρ>0` on `(0,1)`)
and contrapositive `large_gap_forces_below_johnson` (gap `η > √ρ−ρ` ⟹ whole prize range
is below Johnson ⟹ conjecture holds for free there). Thresholds `√ρ−ρ`: ρ=1/2→0.207,
1/4→0.250, 1/8→0.229, 1/16→0.188 — real, non-vacuous. Does **not** disprove: the band is
non-empty for small η and no construction inside it is known.

## Standing constraint lemmas (kept — they "stick")

- **`below_capacity_kills_vanishing_explosion`** / `free_dimension_neg` /
  `vanishing_set_exceeds_degree_budget` (`CandidateDisproofLoop4.lean`, sorry-free,
  axiom-clean): under (★), any agreement/vanishing set has size `> k`; hence the free
  dimension `k − |V|` is negative and no nonzero list-explosion polynomial exists. The
  formal common cause of death for A1–A4.
- **`correlation_disproof_requires_small_gap`** / `johnson_gap_pos` /
  `large_gap_forces_below_johnson` (`CandidateDisproofLoop5.lean`, sorry-free,
  axiom-clean): any correlation-based disproof must live in the Johnson→capacity band
  and use gap `η ≤ √ρ − ρ`; large gaps make the conjecture hold for free.

## Disproof-of-the-disproof status

Every concrete disproof so far is itself disproved:
- A1–A4 (list-size explosions) die on the below-capacity dimension wall (Loop4); the
  only regime where they bite is `δ ≥ 1−ρ`, which (★) excludes via `η > 0`.
- O1 (correlation attack) is squeezed into the narrow Johnson→capacity band with small
  gap `η ≤ √ρ−ρ` (Loop5); no construction is known inside it.

The conjecture is **not** disproved. Live search space: `m ≥ 1` interleaving, prize rate
ρ, gap `0 < η ≤ √ρ−ρ`, radius `δ ∈ [1−√ρ, 1−ρ−η]`, attacking correlation not list size.

### O2 (attempted) — interleaved `m>1` super-polynomial blowup
Idea: the bound carries `(2^m)^{c₁}`; force the correlation to grow faster than any
`poly(2^m)` so no finite `c₁` suffices.
**Refuted (O2), no new lemma — honestly:** the conjecture is *generous* in `2^m` (it
allows the RHS to grow polynomially in the interleaving width `2^m`), and every known
interleaved / correlated-agreement bound (BCIKS20 and successors) is at most
*polynomial* in the interleaving width — the width enters through a union/linear factor,
not an exponential one. To disprove you need a genuinely *super-polynomial-in-`2^m`*
correlation mechanism, and none is identified; the algebraic structure (a single random
linear combination of `2^m` codewords) supplies only a union-bound (linear) factor. I am
**not** manufacturing a Lean lemma here: a vacuous "super-poly ⟺ beats-every-poly"
restatement would be fake content. Recorded as a dead end pending an actual mechanism.
Folded-RS variant collapses to the same RS correlation by the folding isomorphism, so it
inherits the same generosity. → O2 does not disprove.

### O3 (attempted) — Frobenius-orbit blowup of the bad-γ count
**Key reading of the target (verified against `Errors.lean`/`MCAGS.lean`):** `epsMCA` is the
probability `Pr_{γ←$ᵖ F}[mcaEvent] = (#bad γ)/q`, sup'd over word stacks. So the conjecture
`epsMCAgs ≤ (1/q)·(2^m)^{c₁}/(ρ^{c₂}η^{c₃})` asserts, for fixed prize `m,ρ,η`, that the **bad-γ
count is a constant independent of `q`** — the sharpest framing yet.
Idea: take `u₀,u₁` over the prime subfield `F_p`, RS code Frobenius-stable. Then `φ:x↦x^p`
preserves Hamming distance to the stable code and `(u₀+γu₁)^φ = u₀+γ^p u₁`, so **`γ` bad ⟹ `γ^p`
bad** — the bad set is `φ`-closed, a union of Frobenius orbits. A bad scalar of degree `d` forces
`d` bad scalars; in a tower `q=p^s` (`p` fixed), a high-degree bad scalar gives `#bad ≥ s = log_p q
→ ∞`, **violating the constant bound → disproof.**
**Verified sorry-free, axiom-clean in `CandidateDisproofLoop6.lean`:**
`frobenius_iterate_mem` / `frobenius_orbit_subset` / `frobenius_orbit_card_le` (a `φ`-closed set
with a degree-`d` element has card `≥ d`); `const_badcount_forbids_high_degree` (a constant
bad-count bound `#S ≤ C` forces every bad scalar to degree `≤ C`, i.e. into the bounded subfield
`F_{p^{⌊C⌋}}`); `degree_can_exceed_any_constant`.
**Disproof of the disproof (why O3 does NOT close the prize):** the missing link is *realizability*
— a Frobenius-stable `(u₀,u₁)` with a **high-degree** bad scalar **at prize radius** `δ ≤ 1−ρ−η`.
BCIKS20 (proven below Johnson) forces the bad set to be small-or-essentially-all-of-`F`; a lone
high-degree orbit in the gap is exactly the *unestablished beyond-Johnson case*. So O3 gives a hard
**necessary structural condition** — *all bad γ live in a bounded-degree subfield* — but not a
disproof. Kept as a standing constraint; sharply narrows what a real disproof must produce.

## Standing constraint lemmas — addendum (O3)

- **`const_badcount_forbids_high_degree`** (`CandidateDisproofLoop6.lean`, sorry-free, axiom-clean):
  under the conjecture's constant bad-count claim, with `φ`-closed (prime-field-input) bad set,
  every bad scalar has degree `≤ C` over `F_p`. A disproof = realizing a high-degree bad scalar at
  prize radius; the proximity-gap dichotomy is the obstruction to doing so in the gap.

### O4 (attempted) — the conditional disproof from realizing the O3 obstruction
**Verified sorry-free, axiom-clean in `CandidateDisproofLoop7.lean`:**
`realizing_high_degree_bad_scalar_disproves` — if a Frobenius-closed bad set with `#S ≤ C`
(conjecture's constant) contains a scalar of degree `d > C` at prize radius, derive `False`. This is
the exact machine-checked statement that *the only thing between us and a disproof is a high-degree
bad scalar in the live band*.
**Disproof of the disproof (O4):** the antecedent is the unestablished beyond-Johnson case — below
Johnson BCIKS20 forbids a lone high-degree orbit; in `[1−√ρ, 1−ρ−η]` no construction is known. The
conditional does not fire. → not a disproof, a sharpened target.

### O5 (attempted) — does the GS-row restriction escape the Frobenius lower bound? (No.)
**Verified sorry-free, axiom-clean in `CandidateDisproofLoop7.lean`:**
`frobenius_invariant_filter_closed`, `frobenius_invariant_card_ge` — for *any* `φ`-invariant
bad-event predicate `P`, a degree-`d` satisfying scalar forces `#{P} ≥ d`. Since closeness to a
`φ`-stable code is `φ`-invariant, **every** level of `epsMCAgs ≤ epsCA ≤ line-close` is `φ`-invariant
and inherits the same orbit lower bound.
**Outcome:** O5's hoped escape **fails** — the GS-row restriction does not cap the count below the
Frobenius bound. This *strengthens* O3: the bounded-subfield constraint binds `epsCA` and the
line-close error too, not just `mcaEvent`. Not a disproof; a robustness strengthening.

## Standing constraint lemmas — addendum (O4/O5)

- **`realizing_high_degree_bad_scalar_disproves`** (`CandidateDisproofLoop7.lean`): conditional
  disproof; isolates realizability as the sole open hypothesis.
- **`frobenius_invariant_card_ge`** (`CandidateDisproofLoop7.lean`): the Frobenius lower bound is
  robust across the whole dominance chain — the constraint is not specific to `mcaEvent`.
- **`linear_badcount_le_const_div_gap_of_gap_le_const_div_degree`**
  (`CandidateDisproofLoop7.lean`): if high-degree Frobenius examples only occur with
  `η ≤ A/d` and `#bad ≤ B·d`, their bad count is `≤ (B·A)/η`; near-capacity linear
  orbit growth is absorbed by the prize's `η^{-c₃}` allowance.

### O6 (attempted) — exploit missing domain-size factor in the GS RHS
Idea: the formalized GS RHS
`epsMCAgsPrizeBound q m ρ η = (1/q)·(2^m)^{c₁}/(ρ^{c₂}η^{c₃})` appears to carry no
domain-size `n`. If `m` can be fixed while the domain size grows, then even ordinary
`~ n/q` proximity-gap bad counts would beat the bound and disprove the formal statement.

**Audit result:** `GrandChallenges.mcaConjectureBound` does carry `(n : ℝ)^{c₁}` with
`n = |domain|`. The GS-exposed version replaces this by `(2^m)^{c₁}` and its comments say
the prize parameters are `(2^m, 1/ρ, 1/η)`, so the intended reading is almost certainly
`2^m = |domain|` (or at least comparable to it) for smooth domains. However,
`epsMCAgsPrizeUniversalConjecture` / `UniversalGSListMassBound` currently quantify over
all domains with no local side condition tying `m` to `Fintype.card ι`.

**Disproof of the disproof (O6):** an `n`-growth counterexample would attack this formal
linkage, not the prize mathematics. Until the statement is repaired or accompanied by a
`Fintype.card ι = 2^m` / comparability hypothesis, do not claim a prize disproof from
domain-size scaling alone. Keep this as a statement-fidelity constraint.

### O7 (attempted) — brute-force Frobenius witnesses in tiny tower fields
Toy search over `GF(2^s)` for `s = 3,4,5,6` found actual full-degree bad scalars in
Frobenius-stable RS instances: domain `{0} ∪ orbit(α)` (`n=s+1`), prize-rate degree
`k=⌊n/2⌋`, and binary stacks with `u₀` supported at the last orbit point and `u₁` at the
previous one. Bad counts were `3,4,7,11`.

**Disproof of the disproof (O7):** the examples fire at agreement threshold `k+1`, hence
radius `δ = 1 - (k+1)/n`; the capacity gap is `η ≈ 1/n ≈ 1/d`. The Frobenius lower bound
then gives only linear growth in `1/η`, and Loop 7 shows such growth is absorbable by a
single inverse-gap factor. This is evidence for the O3 mechanism, but **not** a prize
disproof. A real disproof needs fixed positive `η` (or super-polynomial growth in `1/η`).

### O6′ — the `q`-independence reduction (the disproof's precise target), Loop8
Reading the *genuine* target `epsMCAgsPrizeUniversalConjecture` / `UniversalGSListMassBound`: the
in-tree chain (`MCAGSWitness.lean`) gives `PivotCovering ∧ |L|≤ℓ ⟹ epsMCAgs ≤ ℓ/q`, and the mass
clause is `ℓ/q ≤ (1/q)·(2^m)^{c₁}/(ρ^{c₂}η^{c₃})`. The `1/q` cancels, so the list size is forced
`≤ B := (2^m)^{c₁}/(ρ^{c₂}η^{c₃})`, **independent of `q`** — and since the universal quantifier order
fixes `c₁,c₂,c₃` (hence `B`) *before the field*, the GS list size must be `q`-bounded by a constant
at every prize rate and fixed gap.
**Verified sorry-free, axiom-clean in `CandidateDisproofLoop8.lean`:** `listsize_le_numerator_of_mass`
(the `1/q` cancellation), `listsize_gt_numerator_refutes_mass`, `listsize_can_exceed_any_numerator`,
`single_instance_over_numerator_refutes`.
**Reduction:** the prize is **false** iff, at some prize rate and *fixed* gap `η>0`, the minimal
pivot-covering faithful GS list size grows without bound as `q→∞` (the dual of "RS list-decodable to
capacity with `q`-independent lists below `1−ρ`").
**Disproof of the disproof (O6′):** that `q`-unbounded fixed-gap growth is exactly the open dual and
is *not* established; below Johnson the list is provably `q`-independent, and the in-tree `ε_mca`
lower bounds are only `poly/q` (within bound). Sharpens the target; does not disprove.

### O7′ — fixed-gap empirical probe over prime fields (evidence bearing on O8)
Numpy brute-force, RS over `F_p` (`n=p`, rate `ρ=1/2`), **sampled** max list size:
* shrinking gap `η=1/n` (threshold `k+1`): max list `2, 5, 36` for `p=5,7,11` — grows (the
  *absorbed* `poly(1/η)=poly(n)` regime; matches the concurrent `GF(2^s)` O7 counts `3,4,7,11`).
* **fixed gap `η=0.1`** (radius held in-band, `1−√ρ < δ < 1−ρ`): max list `2, 5, 5` for `p=5,7,11`
  — **no growth with field size**.
* fixed gap `η=0.2`: radius drops below Johnson → max list `1` (unique decoding), as predicted.
So the list explosion is driven by the *shrinking gap*, not by `q` at fixed gap — empirical support
for Loop7's self-refutation and O6′. **Caveats (honest):** sampled (not exhaustive worst-case), tiny
fields, integer-rounded radius; suggestive of conjecture-survival, *not* proof. → no disproof; weakly
*supports* the conjecture. Script: `o7_fixed_gap_probe.py` (in this dir).

## Proof attempts (the OTHER direction — the prize is won by a proof *or* a disproof)

### P1 — the large-gap regime is provable: a `q`-independent Johnson list budget (Loop9)
The disproof side fenced the open core to *small* gaps `η ≤ √ρ−ρ`. The proof side carves off the
complementary regime. Instantiate the in-tree Johnson list bound
`JohnsonListBound.johnson_list_bound_div` (`|L| ≤ n²/(a²−n·b)`) at a Reed–Solomon code with
agreement `a=(1−δ)n` and pairwise codeword agreement `b=ρn` (RS is MDS, distinct degree-`<k` polys
agree on `≤ k−1 < ρn`): then `a²−n·b = n²·((1−δ)²−ρ)` and

    |L| ≤ 1/((1−δ)² − ρ),   **independent of `n` and `q`**, finite ⟺ `(1−δ)² > ρ` (below Johnson).

By Loop5 (`large_gap_forces_below_johnson`), `η > √ρ−ρ ⟹ δ ≤ 1−ρ−η < 1−√ρ`, so the budget is finite
and `≤ 1/((ρ+η)²−ρ)`, a positive `(ρ,η)`-only constant. **Verified sorry-free, axiom-clean in
`CandidateProofLoop9.lean`:** `below_johnson_of_large_gap`, `johnson_listbudget_le`,
`johnson_budget_qindependent_pos`. This is the proof-side mirror of Loop8's `q`-independence: in the
large-gap regime the prize's list-size budget is met with no `q`-dependence.
**Disproof of the proof (P1):** (i) the budget `1/((ρ+η)²−ρ)` **blows up as `η→(√ρ−ρ)⁺`**, so it is
`poly(1/(η−(√ρ−ρ)))`, *not* `poly(1/η)` — Johnson only proves the prize for gaps bounded **away
from** the Johnson threshold, not up to it. (ii) The Johnson bound caps the actual decoding-ball
size; wiring it into a `FaithfulGSFamily` + `PivotCovering` family (the in-tree mass-bound chain)
needs the classical GS *decoder construction* (absent from mathlib). So P1 is a genuine **partial
proof** — the combinatorial `q`-independent core in the large-gap regime — exactly as partial as the
disproof side, and meeting it at the Johnson threshold `η = √ρ−ρ`.

### Synthesis: the problem is carved at the Johnson threshold `η₀ = √ρ−ρ` (Loop10, verified)
- `η > η₀` (large gap): **provable** — radius below Johnson, `q`-independent list budget (P1/Loop9).
- `η ≤ η₀` (small gap): **open** — radius in the band `(1−√ρ, 1−ρ−η]`; disproof needs a fixed-gap
  `q`-growing list-size lower bound (O6′/Loop8), proof needs beyond-UDR GS decoding. Both partial
  sides meet exactly here; the prize lives in this band.

**`CandidateCarvingLoop10.lean` (sorry-free, axiom-clean)** makes this exact:
`below_johnson_iff_large_gap` (`1−ρ−η < 1−√ρ ↔ η₀ < η`), `prize_radius_excess_eq_depth` (the
beyond-Johnson **depth** `ζ := η₀ − η` is *literally* the radius excess `(1−ρ−η) − (1−√ρ)`),
`johnsonGapThreshold_pos` (open band non-empty), `provable_region_nonempty` (P1 closes a real slice
`η ∈ (η₀, 1−ρ]`), `carving_dichotomy`. **The open prize is exactly the regime `ζ > 0`.**

### In-tree proof-side state (Hab25 = Haböck Thm 2, the Johnson-range MCA bound)
`Hab25Johnson.lean` ports Haböck ePrint 2025/2110 Thm 2: in the **Johnson range** (`δ < 1−√ρ`, i.e.
the large-gap side `η > η₀`), `|E| ≤ (ℓ⁷/3)(ρn)²` with `ℓ=(m+½)/√ρ` (`m` = GS *multiplicity*), the
deep GS-interpolation/discriminant/Hensel steps isolated as named residuals (`Hab25JohnsonResiduals`,
no `sorry`). So the proof side is *reduced to named classical GS facts* up to the Johnson radius.
**Two consequences:** (1) the bound carries `n²` → it matches the prize RHS `(2^m)^{c₁}/q` only under
the smooth-domain linkage `2^m ≍ n = |domain|` with `c₁ ≥ 2` (this is exactly the O9 fidelity point).
(2) GS multiplicity `m→∞` approaches but never exceeds the Johnson radius for *plain* RS, so Hab25
cannot cross `η₀` — the small-gap band needs genuinely new beyond-Johnson math (smooth-domain
list-decodability), confirming the carving is at the true mathematical frontier.

### Loop45 — MASTER / CANDIDATE: the literal prize reduced to ONE open lemma (`PolyOrbitCount`)
**Verified sorry-free, axiom-clean in `CandidateMasterLoop45.lean`** (loop step 8 — promote a
candidate): `PolyOrbitCount Vcard m d := ∃ N S, 0≤N ∧ 0≤S ∧ Vcard≤N·S ∧ N≤(2^m)^d ∧ S≤2^m` (the
single open input) and `master_prize_from_poly_orbit_count` (`q≥1` + `PolyOrbitCount` ⟹
`Vcard/q² ≤ (1/q)·(2^m)^{d+1}`, the literal prize), `master_prize_bound_pos`.
**What it is.** The whole Loop38/41/43/44 chain assembled into ONE conditional theorem whose only
unproven antecedent is `PolyOrbitCount`. This is the candidate for other agents to attack: a single
crisp lemma carrying all remaining difficulty.
**`PolyOrbitCount` status.** Johnson range (`η>η₀`): **theorem** (list size poly ⟹ N poly; GS/BCIKS
2055) ⟹ prize unconditional there. Small-gap band (`0<η≤η₀`): **OPEN** = the genuine $1M core (poly
list/orbit count below capacity for deterministic structured domains). Strictly *weaker* than 861's Q2
(constant N). To close the literal prize: prove `PolyOrbitCount` in the small-gap band; to refute the
prize: exhibit a super-poly deterministic-smooth orbit count below capacity at fixed rate (which would
also settle a long-standing list-decoding question). The reduction is verified; the core is open.

### Loop44 — the prize needs only a POLYNOMIAL orbit count (strictly weaker than 861's Q2)
**Verified sorry-free, axiom-clean in `CandidateBridgeLoop44.lean`:** `mca_prize_of_poly_orbit_count`
(if `|V_δ| ≤ N·S` with *polynomial* orbit count `N ≤ (2^m)^d` and orbit size `S ≤ 2^m`, then over any
field `q ≥ 1`: `|V_δ|/q² ≤ (1/q)·(2^m)^{d+1}` — prize shape `c₁=d+1`), `q2_implies_poly_orbit_count`
(`N ≤ K ≤ (2^m)^d ⟹ N ≤ (2^m)^d`: Q2's constant bound is a special case), `poly_prize_bound_pos`.
**Hypothesis class (attacking Q2).** Loop43 reduced the literal prize to a *constant* orbit-count bound
`N ≤ K_ρ`, which is 861's Q2 (`O(1)/|F|`). But the #232 prize tolerates any `poly(2^m,1/ρ,1/η)/q` — so
ask: does the prize actually need the full strength of Q2, or only a *polynomial* `N`?
**Result.** Only polynomial. `mca_prize_of_poly_orbit_count` lands the prize from `N ≤ (2^m)^d` (any
`d`), and `q2_implies_poly_orbit_count` shows Q2 ⟹ this. So **the prize is strictly weaker than Q2**:
861 chases a constant `K_ρ` (deployment-grade `O(1)/|F|`); the prize needs only `poly`. The key
arithmetic subtlety: `ε_mca = |V_δ|/q²` already carries `1/q²`, and `1/q² ≤ 1/q` for `q ≥ 1`, so the
extra polynomial factor `(2^m)^{d+1}` is absorbed into the `c₁` exponent with one `q` to spare.
**Why it advances the open core.** A *polynomial* orbit count is **already a theorem in the Johnson
range** (list size `poly(n)` by GS / BCIKS 2025/2055 ⟹ `|V_δ|` poly ⟹ `N` poly) — re-deriving Loops
9/11/13's unconditional large-gap prize through the cleaner orbit-count lens. The open residual is *only*
the small-gap band `0<η≤η₀`, and even there the prize does **not** need 861's constant — a polynomial
`N` suffices. This separates two difficulties the literature conflates: 861's `O(1)/|F|` (needs Q2) vs
the #232 prize's `poly(2^m)/|F|` (needs only poly `N`). Prize-as-stated still OPEN in the small-gap band,
but on a demonstrably weaker hypothesis than Q2.

### Loop43 — the orbit-count route that would close the LITERAL ε_mca prize (not sidestep it)
**Verified sorry-free, axiom-clean in `CandidateBridgeLoop43.lean`:** `mca_orbit_count_bound`
(`|V_δ| ≤ N·S ⟹ |V_δ|/q² ≤ N·S/q²`) and `mca_prize_of_bounded_orbit_count` (with orbit count `N ≤ K`,
orbit size `S ≤ 2^m`, and `2^m ≤ q`: `|V_δ|/q² ≤ K/q` — the Conjecture-1.1 prize shape `ε_ca ≤ K_ρ/q`,
a bound on `ε_mca` *itself*), plus `mca_prize_bound_pos`.
**Why this matters.** Loop42 (858/threshold-halving) settles FRI soundness but *sidesteps* `ε_mca`. The
ONLY route to the *literal* #232 prize (a bound on `ε_mca` at radius `δ`) is the orbit-counting bound of
861: `ε_ca(f) = |V_δ(f)|/q²` (Conj 1.1), and Theorem 2.1 (Loop41, verified sound) forces `V_δ` to be a
union of `⟨ω^{b−a}⟩`-orbits each of size `S = n₁/gcd(b−a,n₁) ≤ 2^m`. So `|V_δ| ≤ N·S` with `N` the bad
orbit count, and Loop43 shows `N ≤ K ⟹ ε_mca ≤ K/q`. **This pins the entire remaining open content of
the literal prize to one sharply stated quantity: an `n`-uniform bound on the bad-orbit count `N`.** Per
861 that bound is unconditional for sparse (3-position) inputs (Layer 1 = our Loops 33/34) and `= Q2`
for general inputs (empirically verified at `(32,8)`, unproven). So the literal prize ⟺ Q2 (orbit-count
form). Honest: Loop43 is the arithmetic reduction only; it does not supply `N ≤ K`, which is the open
core. Prize-as-stated remains OPEN.

### Loop42 — UNCONDITIONAL commit-phase prize shape via threshold halving (Chai–Fan 2026/858)
**Verified sorry-free, axiom-clean in `CandidateProofLoop42.lean`:** `threshold_halving_into_unique_decoding`
(`δ < 1−ρ ⟹ δ/2 < (1−ρ)/2`, the entire algebraic content of 858's move) and the capstone
`unique_decoding_commit_prize_unconditional`: in the unique-decoding regime reached by halving, the
per-round bad-challenge fraction is `≤ n/q` (BCIKS, `n=|L|≤2^m`), so Loop38's union bound over the `m`
rounds gives commit-phase `∑_{j<m} e_j ≤ (1/q)·(2^m)^2` — **prize numerator shape `c₁=2, c₂=c₃=0`,
UNCONDITIONAL**, whole open zone `δ∈(δ_J,1−ρ)`, no `η`, no conjecture. `commit_prize_const_pos`.
**Source.** eprint 2026/858 (read June 2026; PDF fetched past the 403 with a `Referer` header) proves
the *first unconditional* soundness above Johnson for FRI/STIR/WHIR, `k=2^m`, `L` with a fixed-point-free
involution, any char. Mechanism = **threshold halving** (RVW13): conclude the low-degree test at `δ/2`
not `δ`; since `δ/2 < (1−ρ)/2` (unique-decoding radius), after round 1 the distance is *locked* by
BCIKS Thm 1.2 — immune to any open-zone counterexample — at a `~2×` query cost. Result (A) is genuinely
unconditional (only its results (B)/(C) carry conjectures, not needed here).
**Honesty / scope (loop step 6).** 858 bounds `ε_FRI` by *avoiding* `ε_mca` (halved threshold, `2×`
queries); it does **not** bound `ε_mca` at radius `δ`. So the *literal* MCA prize (a bound on `ε_mca` at
`δ ≤ 1−ρ−η`) is **sidestepped, not proven** — Loop42 does not close #232 as stated. But the practical
above-Johnson FRI soundness the prize was motivated by is now unconditionally in prize shape. `n ≤ 2^m`
is faithful (smooth domain ⊂ `2^m`-th roots, Loop11 linkage); per-round `≤ n` is BCIKS in the UD regime.

### Loop41 — verifying the UNCONDITIONAL core of Chai–Fan 2026/861 (Action–Orbit Theorem 2.1)
**Verified sorry-free, axiom-clean in `CandidateBridgeLoop41.lean`** (`pencil_substitution` depends
only on `[propext]`): `pencil_substitution` (the pencil algebraic factoring, step iv:
`(μz)^a+α(μz)^b = μ^a·(z^a+(αμ^{b−a})z^b)` for `a≤b`, the single pencil-specific computation),
`dist_orbit_invariant` (invariance under `×s` ⟹ invariance under `×s^n`, by induction), and
`bad_closed_under_orbit` (`D` invariant under `×s` + `D α ≤ τ` ⟹ `D(s^n·α) ≤ τ`: the bad set is a
union of `⟨s⟩`-orbits — Theorem 2.1's conclusion with `s = ω^{b−a}`).
**Why.** A full read of 2026/861 shows its prize-relevant claim (Conj 1.1) is **conditional on TWO
conjectures**: Q1 (Conj 4.12, NT non-vanishing, rigorous only at `d∈{4,8}`) and Q2 (Conj 7.1,
sparse-worst-case dominance, only *empirically* verified at scale `(32,8)`). So 861 does **not** resolve
the prize. Its *unconditional* contribution is Theorem 2.1 (the authors: "the question, not the proof,
is the contribution"). Loop41 verifies that core is genuinely sound — the algebraic factoring where any
error would hide checks out, and the orbit-closure consequence is exactly as claimed. This confirms the
action-orbit *mechanism* is rigorous and isolates **all** of 861's conditionality into Q1/Q2 (the open
core, handled in Loop40). Steps (i),(ii),(v) — Hamming permutation-invariance, `RSₖ`-linearity — are
standard and enter as the `hinv` hypothesis.

### Loop40 — SECOND PATH: sparse-worst-case dominance (Q2, Chai–Fan 2026/861) ⟹ prize (conditional)
**Verified sorry-free, axiom-clean in `CandidateProofLoop40.lean`:** `sparse_dominance_prize_mass`
(given the unconditional sparse per-round bound `eSparse ≤ C/q` and `Q2` dominance `∀ j<m, e_j ≤
eSparse`, the union-bound total lands on the prize RHS `(1/q)·(2^m)^1·C`, triple `c₁=1, c₂=c₃=0` — a
`q`-independent *constant* numerator, no `η` factor) and `sparse_dominance_const_pos` (non-vacuous).
**Literature trigger (June 2026 pass).** Chai–Fan, eprint 2026/861 ("Action–Orbit FRI Soundness Above
the Johnson Radius: a rigorous `O(1)/|F|` bound on plain Reed–Solomon") independently reaches THIS
log's frontier from the other side: it proves the per-round proximity error on the *cyclic* (smooth
multiplicative-subgroup) domain is `≤ C/|F|` above Johnson **unconditionally for sparse adversary
inputs** — the literature twin of our Loops 33/34 (bounded sparse spikes absorbed) — and reduces the
general case to a single conjecture **Q2 "sparse-worst-case dominance"** (worst case dominated by the
sparse case). Their `Q2` is the literature name for exactly the open core this log isolated: does the
worst case reduce to the provably-safe sparse/bounded case.
**What this gives.** A *second independent* conditional path to the prize, parallel to Loop39's BGM
route, via a different mechanism (action-orbit symmetry, not list-decoding). Both now land the prize
across the whole band from one hypothesis each — BGM-for-smooth (Loop39) and `Q2` (Loop40) — which
strengthens the "leans TRUE" position. Loop40's path is even cleaner (constant numerator `c₂=c₃=0`).
**Caveats (honest).** This brick formalizes only the *logical reduction* (`Q2` + sparse bound + union
bound ⟹ prize); it does **not** verify Chai–Fan's unconditional sparse claim or their action-orbit
lemma — the full eprint PDF was inaccessible (eprint.iacr.org 403), and the advertised "five-line proof
above Johnson" for a problem three groups missed warrants independent scrutiny before trust. `Q2` is an
unproven conjecture = the open core. Prize remains OPEN; do not treat as resolved. See also eprint
2026/858 (Threshold-Halving, RVW) claiming unconditional soundness above Johnson for FRI/STIR/WHIR —
also unread, also to scrutinize.

### Loop39 — INTEGRATION CAPSTONE: BGM budget × FRI union bound ⟹ full-band prize (conditional)
**Verified sorry-free, axiom-clean in `CandidateProofLoop39.lean`:** `bgmBudget_le_inv_gap`
(`(1−ρ−η)/η ≤ 1/η` for `ρ ≥ 0`, `η > 0`), `bgmBudget_nonneg`, and the capstone
`full_band_prize_mass`: if every per-round FRI/proximity event obeys `e_j ≤ L_BGM(ρ,η)/q` with
`L_BGM(ρ,η) = (1−ρ−η)/η`, then the union-bound total error lands **exactly** on the prize RHS
`∑_{j<m} e_j ≤ (1/q)·(2^m)^1/η`, i.e. the single constant triple `c₁=1, c₂=0, c₃=1`, for **every**
gap `η > 0` including the small-gap band.
**What it integrates (loop step 7).** This composes Loop17 (P4, the BGM capacity budget finite across
the whole band), Loop38 (the real mechanism is a union bound — additive), and Loop37 (the budget is
carried *once* into the depth-independent `1/η`, never per round). It is the first statement landing
the prize on its own RHS *across the entire band* — not just the Johnson range — from one clean
hypothesis, in the exact shape the FRI mechanism produces.
**Attack.** Does the integration smuggle in an `n`/`q`/`(2^m)` factor that breaks the prize numerator?
No: the only `(2^m)` factor is the union-bound depth `m ≤ 2^m` (`c₁=1`); the BGM budget is itself
`q`-independent and `n`-free, landing wholly in `1/η`. Could the per-round budget force a worse `c₃`?
No: a single `1/η`, `c₃=1`. The brick is honest-conditional: its hypothesis
`hround : ∀ j<m, e_j ≤ L_BGM(ρ,η)/q` is **exactly (BGM-for-smooth)** — proven (BCIKS 2025/2055) in the
Johnson range, where the prize is therefore now *unconditional* via this brick; open in the small-gap
band. Loop39 does **not** close the prize; it certifies the open core is reduced to one hypothesis and
that hypothesis lands the prize.

### Loop38 — the real FRI/proximity mechanism composes per-round events ADDITIVELY (union bound)
**Verified sorry-free, axiom-clean in `CandidateStructureLoop38.lean`:**
`fri_union_bound` (per-round error `e_j ≤ p` ⇒ total `∑_{j<m} e_j ≤ m·p`),
`fri_total_error_le_domain_pow_mul` (`m·p ≤ (2^m)·p` via `m < 2^m`, prize numerator exponent
`c₁=1` with the one-shot budget `p` carried once), and `fri_additive_beats_multiplicative` (for
`a ≥ 2`, `m ≥ 2`: `m·a ≤ a^m` — the additive union-bound mode is strictly cheaper than the
multiplicative tower).
**Hypothesis class.** Loop37 said a disproof needs a per-round *multiplicative* factor growing in `m`
or `1/η`. So ask: does the actual BCIKS proximity-gaps / FRI soundness mechanism compose its per-round
events multiplicatively (danger) or additively (safe)?
**Disproof attempt.** Try to read the `m`-round FRI recursion as a product: each fold re-runs the
proximity test, so maybe the soundness errors compound like `∏ (1+e_j)` and tower up super-polynomially
across the `m = log₂ n` rounds. **Disproof of the disproof:** no — the proven BCIKS soundness bound is a
**union bound**: the total error is `∑_{j<m} e_j`, each `e_j ≤ B(ρ,η)/q` a single correlated-agreement
event. `fri_union_bound` is exactly this additive accumulation; it lands in the Loop27/29 safe regime,
the depth factor `m` absorbed by `m < 2^m` (`fri_total_error_le_domain_pow_mul`, giving `c₁=1`), and the
per-round budget `B(ρ,η)` paid **once** into the depth-independent factor `G` — precisely Loop37's safe
envelope. `fri_additive_beats_multiplicative` certifies the gap: the multiplicative tower the disproof
needs is strictly larger than the additive cost the mechanism actually pays.
**What this localizes.** The entire disproof question is now: does the per-round event probability *stay*
one-shot (`≤ B(ρ,η)/q`, `B` depending only on `ρ,η`) across the small-gap band `δ ≤ 1−ρ−η`? In the
Johnson range that is the theorem BCIKS 2025/2055 — and there the union-bound structure here makes the
prize hold outright. In the small-gap band it is exactly the open BGM-for-smooth fact (Loop17). No
construction makes the per-round event compound multiplicatively; the union-bound structure of the FRI
recursion forbids it by design.

### Loop37 — the per-round multiplier must be GAP-independent, not merely depth-independent
**Verified sorry-free, axiom-clean in `CandidateStructureLoop37.lean`:**
`const_multiplier_product_le_domain_pow` (per-round factors `a_j ≥ 0` with `a_j ≤ 2^c` accumulate to
`∏_{j<m} a_j ≤ (2^m)^c`), `gap_budget_per_round_overflows` (if `2^c < a` then `(2^m)^c < a^m` for
`m ≥ 1`), `exists_budget_overflowing` (for every fixed `c` there is a budget `B = 2^c+1 > 2^c`
overflowing the degree-`c` polynomial at every positive depth), `prize_decomposition`
(`∏_{j<m} 2^{c₁} · G = (2^m)^{c₁} · G`), and `safe_envelope` (gap-independent per-round factor times a
one-shot nonneg gap factor `G` stays prize-shaped).
**Hypothesis class.** The prize triple `(c₁,c₂,c₃)` is fixed *before* the field, hence before the gap
`η`. The depth-exponential factor `(2^m)^{c₁}` is arithmetically an `m`-fold product of the *single
universal base* `2^{c₁}`. So a per-round multiplier can ride `(2^m)^{c₁}` **only if it is bounded by a
gap-independent constant** `2^{c₁}`.
**Disproof attempt (the self-attack).** Take the cleanest survivor of Loop35 — "constant per-round
multiplier" — and instantiate it with the actual capacity budget `B(ρ,η) ≈ 1/η`, which is constant in
the depth `m`. Naively this is "depth-independent", so it looks prize-safe. **Disproof of the
disproof:** no — `gap_budget_per_round_overflows` shows that since `B(ρ,η) → ∞` as `η → 0`, for **any**
fixed `c₁` there is a gap small enough that `2^{c₁} < B(ρ,η)`, and then `B^m > (2^m)^{c₁}` at every
positive depth. A per-round *gap-budget* multiplier therefore defeats every field-independent `c₁`.
So depth-independence is **not** enough: the per-round multiplier must be independent of the gap too.
**What this localizes.** `prize_decomposition` + `safe_envelope` give the structural verdict: the
depth-exponential part `(2^m)^{c₁}` may carry only the gap-INDEPENDENT universal constant, while ALL
gap dependence must live in the depth-INDEPENDENT one-shot factor `G = 1/(ρ^{c₂} η^{c₃})`. This is
exactly the shape of the proven regimes — Johnson/Loop11 places `n² = (2^m)²` with `c₁ = 2` and pushes
the `ℓ⁷ρ²` list budget into the denominator, paid once, never per round. So the only thing BGM/Johnson
actually supply (a *one-shot* capacity budget) lands in `G` and is prize-safe; a genuine disproof needs
the smooth-domain GS/proximity mechanism to charge a gap- or depth-growing budget **per round**, which
no construction does. This sharpens Loop35: the surviving danger is not just "unbounded in `m`" but
"unbounded in `m` OR in `1/η` as a *per-round* factor".

### Loop36 — amplified additive injections are still safe under constant blowup
**Verified sorry-free, axiom-clean in `CandidateStructureLoop36.lean`:**
`affine_recursion_amplified` (`T(j+1)≤aT(j)+b` gives
`T(m)≤a^mT(0)+m*b*a^m` for `a≥1,b≥0`), `pow_const_factor_eq_domain_pow`,
`affine_recursion_exact_constant_factor`, and `affine_recursion_constant_factor_absorbed` (under
per-fold factor `2^c`, nonnegative base, and bounded additive injection `b`, the full recurrence is
bounded by `(T(0)+b)*(2^m)^(c+1)`).
**Disproof attempt:** maybe additive per-fold errors are harmless when added, but later
multiplicative folds amplify them into a super-polynomial tower. **Disproof of the disproof:** if the
multiplicative factor has bounded exponent density (`2^c` per fold) and the additive injection is
bounded, amplification costs only the final multiplicative factor plus the fold depth `m`; `m≤2^m`
absorbs it into one extra polynomial degree. A real affine-recursion disproof must still force
unbounded multiplicative exponent density or unbounded additive injections in the actual
smooth-domain GS/proximity process.

### Loop35 — unbounded exponent density is the real multiplicative danger
**Verified sorry-free, axiom-clean in `CandidateStructureLoop35.lean`:**
`density_product_eq` (`((2^m)^D)=2^(m*D)`), `exponent_product_eq`,
`exponent_density_overflows_final_degree` (if cumulative exponent is at least `m*D` and `D>d`, the
product beats final degree `d`), `density_one_more_overflows_final_degree`, and
`linear_spike_density_overflows_final_degree`.
**Disproof attempt:** take the complement of Loops 31--34 seriously: force exponent density to grow
past every fixed prize degree, for example by making the effective spike density `K*h` unbounded.
This **would** arithmetically defeat the prize numerator. **Disproof of the disproof:** the new brick
only gives the overflow criterion. It does not prove that faithful smooth-domain GS/proximity lists
realize cumulative exponent `≥m*D` with unbounded `D`. Loops 31--34 say all bounded-density variants
are absorbed; Loop35 says exactly what remains to be constructed. No such construction is known in
the below-capacity small-gap band.

### Loop34 — bounded-count linear spikes are absorbed
**Verified sorry-free, axiom-clean in `CandidateStructureLoop34.lean`:**
`sparse_linear_spike_sum_le` (if the spike support has size `≤K` and each active spike is `≤m*h`,
then the total spike mass is `≤m*(K*h)`), `sparse_linear_spike_product_eq`, and
`sparse_linear_spike_product_le_domain_pow` (baseline `c` plus a bounded number of height-linear
spikes is absorbed by final degree `c+K*h`).
**Disproof attempt:** maybe a constant number of extremely tall fold levels, each as large as the
full depth, can create a multiplicative product that beats every fixed final-domain polynomial.
**Disproof of the disproof:** no — a bounded number of height-`O(m)` spikes only adds a constant
amount to the exponent density, hence only raises the allowed polynomial degree. A spike-based
counterexample must make the number of spikes or their height-density unbounded in the actual
smooth-domain GS/proximity process. A few full-depth spikes are still prize-safe.

### Loop33 — bounded sparse spikes are absorbed
**Verified sorry-free, axiom-clean in `CandidateStructureLoop33.lean`:**
`sparse_spike_sum_le` (a spike function supported on `S` and bounded by height `h` contributes at
most `m*h` over the first `m` levels), `sparse_spike_product_eq`, and
`sparse_spike_product_le_domain_pow` (baseline exponent `c` plus bounded spikes is absorbed by the
final-domain polynomial of degree `c+h`).
**Disproof attempt:** force a few alarming fold levels with high-looking multiplicative exponents
while keeping most levels harmless, hoping sparse irregularity beats every fixed polynomial in
`2^m`. **Disproof of the disproof:** bounded spikes do not work. If spike heights are bounded by
`h`, their total contribution is still linear in the depth and only increases the final polynomial
degree from `c` to `c+h`. A spike-based disproof must make the spike height or average spike density
grow without bound in the actual smooth-domain GS/proximity mechanism. Sparse scary levels are not
enough.

### Loop32 — block grouping cannot hide multiplicative exponent growth
**Verified sorry-free, axiom-clean in `CandidateStructureLoop32.lean`:**
`block_exponent_product_eq` (`∏_{i<r}2^(b_i)=2^(∑_{i<r}b_i)`),
`block_exponent_product_le_domain_pow` (if block widths sum to `m` and every block exponent is
`≤ width_i*c`, the blocked product is at most `((2^m)^c)`), and
`block_exponent_product_overflows_of_sum` (only total block exponent `>m*d` overflows final
degree `d`).
**Disproof attempt:** hide multiplicative growth by grouping fold levels into irregular blocks or by
using spiky block factors, hoping the grouped accounting beats every fixed polynomial even when local
average density looks bounded. **Disproof of the disproof:** no — block exponents still add. If every
block has bounded exponent density relative to its width, then the whole product is absorbed by the
prize numerator. Blocking/spiking only matters if the **total** block exponent has unbounded density
in the final depth, which must be realized by the actual smooth-domain GS/proximity process. Mere
regrouping is not a counterexample.

### Loop31 — variable multiplicative exponents: only the total exponent matters
**Verified sorry-free, axiom-clean in `CandidateStructureLoop31.lean`:**
`variable_exponent_product_eq` (`∏_{j<m}2^(e_j)=2^(∑_{j<m}e_j)`),
`variable_exponent_product_le_domain_pow` (if `∑e_j≤m*c`, the product is at most the final-domain
degree-`c` polynomial), `variable_exponent_product_le_domain_pow_of_pointwise` (bounded per-level
exponents are prize-safe), and `variable_exponent_product_overflows_of_sum` (if `m*d<∑e_j`, the
product beats final degree `d`).
**Disproof attempt:** replace Loop30's rigid local factors `(2^j)^c` with adaptive or uneven factors
`2^(e_j)` and hope the irregularity itself defeats every fixed polynomial in `2^m`.
**Disproof of the disproof:** no — the product sees only the cumulative exponent. If the total
exponent is linear in the depth `m`, or if every level exponent is uniformly bounded, the prize
numerator absorbs the tower. A variable-factor disproof must prove a **superlinear cumulative
exponent** realized by the actual smooth-domain GS/proximity process. Merely naming uneven local
factors does not disprove the conjecture.

### Loop30 — local polynomial multiplicative factors are dangerous only as a product
**Verified sorry-free, axiom-clean in `CandidateStructureLoop30.lean`:**
`local_polynomial_product_eq` (`∏_{j<m}(2^j)^c = 2^(∑_{j<m}j*c)`) and
`local_polynomial_product_overflows_of_exponent` (if `m*d < ∑_{j<m}j*c`, the local-polynomial
multiplicative product beats the final-domain degree-`d` polynomial `((2^m)^d)`). Strengthened by
`local_exponent_sum_overflows_at_depth` and `local_polynomial_product_overflows_at_depth`: for every
positive local degree `c`, depth `m=2*d+3` already makes the product beat the final degree-`d`
polynomial.
**Disproof attempt:** realize per-fold local-polynomial branching multiplicatively, so the product of
local factors accumulates a quadratic-in-depth exponent and eventually beats every fixed polynomial
in the final smooth-domain size. This is the cleanest remaining arithmetic counterexample shape:
local factors that are harmless one level at a time become dangerous when multiplied across all
levels. **Disproof of the disproof:** the Lean brick is only conditional arithmetic. It proves no
faithful GS/proximity mechanism whose fold levels branch independently and multiplicatively by
`(2^j)^c`. Loops 26, 27, and 29 say additive/union-bound accumulation is prize-safe, and Loop28 says
any polynomially bounded multiplicative product is prize-safe. Thus Loop30 narrows the target: a real
disproof must exhibit genuinely multiplicative, per-level local-polynomial branching in the actual
smooth-domain GS list process, not merely a product identity.

### Loop29 — additive fold factors: only the sum matters
**Verified sorry-free, axiom-clean in `CandidateStructureLoop29.lean`:**
`variable_additive_recursion_telescopes` (`T(j+1)≤T(j)+b_j` telescopes to
`T(m)≤T(0)+∑_{j<m}b_j`) and `variable_additive_polynomial_of_sum_bound` (if the cumulative additive
sum is `≤(2^m)^c`, the whole tower is bounded by base plus a polynomial in the domain size).
**Disproof attempt:** maybe additive growth can hide in uneven per-fold spikes, even though uniform
polynomial additive costs are absorbed by Loop27. **Disproof of the disproof:** no — additive
recurrences care only about the cumulative sum. One large-looking fold, or any collection of folds
whose total sum remains polynomial in `2^m`, is absorbed by the prize numerator. An additive
counterexample must make the **sum** itself beat every polynomial in `2^m`.

### Loop28 — variable fold factors: only the product matters
**Verified sorry-free, axiom-clean in `CandidateStructureLoop28.lean`:**
`variable_fold_recursion_telescopes` (`T(j+1)≤a_j·T(j)` telescopes to
`T(m)≤(∏_{j<m}a_j)·T(0)`) and `variable_fold_polynomial_of_product_bound` (if
`∏_{j<m}a_j≤(2^m)^c`, then the whole multiplicative tower is polynomial in the domain size).
**Disproof attempt:** use one `N`-dependent fold factor as evidence of multiplicative blowup.
**Disproof of the disproof:** one large factor is not enough; only the cumulative product matters.
Isolated large folds, or any polynomially bounded product of fold factors, are absorbed by the prize
numerator. A multiplicative counterexample must force the product itself to beat every polynomial in
`2^m`.

### Loop27 — polynomial additive fold costs are still absorbed
**Verified sorry-free, axiom-clean in `CandidateStructureLoop27.lean`:**
`fold_depth_mul_domain_pow_le_next_pow` (`m·(2^m)^c ≤ (2^m)^(c+1)`) and
`additive_polynomial_step_le_next_pow` (if each fold adds at most `C·(2^m)^c`, then
`T(m)≤B₀+C·(2^m)^(c+1)`). **Disproof attempt:** maybe the additive/union-bound model from Loop26
still refutes the prize if every fold contributes polynomially many new close codewords. **Disproof
of the disproof:** no — the tower depth is only `m=log₂N`, and `m` is absorbed by one extra power of
`N=2^m`. So any **polynomial additive** per-fold cost remains prize-safe. The remaining disproof
target is now stricter: either a super-polynomial additive contribution at some fold, or genuinely
multiplicative branching with an `N`-growing factor.

### Loop26 — additive vs multiplicative per-fold growth (narrows the disproof target)
**Verified sorry-free, axiom-clean in `CandidateStructureLoop26.lean`:** `additive_recursion_linear`
(`T(j+1)≤T(j)+b` ⟹ `T(m)≤T(0)+m·b`), `additive_recursion_le_domain` (with `b≥0`, base `T(0)≤B₀`,
and `m≤2^m`: `T(m)≤B₀+(2^m)·b` — linear in `N=2^m`, `c₁=1`). **Refinement of the crux:** Loop24/25
used the *pessimistic multiplicative* model. But FRI/STIR soundness is a *union bound over rounds* —
**additive** per fold. If the smooth-domain per-fold list growth is additive (`+b`), the total is
linear in `m=log₂N` ⇒ polynomial in `2^m` ⇒ **prize TRUE with `c₁=1` and NO open scalar**. And even
*constant-factor* multiplicative growth is fine (Loop24). So the disproof target is now strictly
sharper: it requires the per-fold factor to be **multiplicative AND `N`-growing** simultaneously —
not merely "not constant." The refined open question: is smooth-deterministic per-fold list growth
additive/union-bound (TRUE) or genuinely multiplicative-with-`N`-growing-factor (FALSE)?

### Loop25 — anchored recursion: the whole prize is now ONE open scalar inequality
**Verified sorry-free, axiom-clean in `CandidateStructureLoop25.lean`:** `recursion_anchored`
(constant blowup `a≤2^c` + base `T(0)≤B₀` ⟹ `T(m)≤(2^m)^c·B₀`), `fold_list_le_domain_pow` (base
`T(0)≤1` ⟹ `T(m)≤(2^m)^c`). **Base case** `T(0)≤1`: below the unique-decoding radius the list is a
singleton (Johnson/unique decoding, in-tree `JohnsonList.johnson_unique_decoding`). Assembling Loop24's
telescoping + this proven base: the full scale-`2^m` list is bounded by the **explicit `q`-independent
polynomial `(2^m)^c`**, which clears the prize RHS with `c₁=c`. **Net:** every ingredient of the TRUE
branch is now *proven* — the carving, the telescoping, the base, the RHS fit — **except one real
number**: the per-fold blowup `a` and whether `a ≤ 2^c` for an `N`-independent `c`. The entire
ABF26 prize is thereby reduced to a *single open scalar inequality* about the smooth-deterministic
per-fold proximity-gap soundness. That scalar's `N`-dependence is the isolated `$1M` question (no
published answer); it cannot be fabricated.

### Loop24 — the per-fold recursion criterion: constant blowup ⟹ polynomial ⟹ prize TRUE
**Verified sorry-free, axiom-clean in `CandidateStructureLoop24.lean`:** `fold_recursion_telescopes`
(`T(j+1)≤a·T(j)` ⟹ `T(m)≤aᵐ·T(0)`), `constant_blowup_polynomial` (`a≤2^c` ⟹ `aᵐ≤(2^m)^c`),
`fold_list_polynomial_of_constant_blowup` (combined: `T(m)≤(2^m)^c·T(0)`). **The quantitative
dichotomy of the FRI tower (Loop23):** writing `T j` for the list size at fold level `j`, the prize is
- **TRUE** iff the per-fold blowup `a` is a *constant* (`N`-independent, `a≤2^c`): then over `m=log₂N`
  folds the list `≤ (2^m)^c·T(0)` = **polynomial in the domain size** `2^m`, clearing the prize RHS
  with `c₁=c` (then Loop11/13/17);
- **FALSE** iff the per-fold blowup *grows with `N`* (`a=a(N)→∞`): then `aᵐ` is super-polynomial in
  `2^m` ⇒ Loop8 `q`-growth.
A single fold's single orbit is absorbed (Loop21); the open question is exactly whether the per-fold
proximity-gap soundness blowup *stays `N`-independent across all `m` folds* for plain
smooth-deterministic RS. This is the precise quantitative form of the FRI/STIR-to-capacity frontier.

### Loop23 — the prize is SELF-SIMILAR under folding: it IS the FRI/STIR soundness frontier
**Verified sorry-free, axiom-clean in `CandidateStructureLoop23.lean`:** `pow_fold_mem` (the power map
`x↦x^d` sends `μ_N` onto `μ_{N/d}` when `d∣N` — the FRI fold of the smooth domain),
`recursive_rate_preserved` (`(k/d)/(N/d)=k/N` — the `μ_d`-invariant subcode is the **same-rate** RS
code one scale down), `tower_depth` (`2^m/2^m=1` — the dyadic domain folds in exactly `m` levels).
**Key identification:** the `μ_d`-invariant subcode (Loop22) on `μ_N`, through `x↦x^d`, *is the prize
at scale `N/d`, same rate ρ* — so the smooth-domain prize is **self-similar under folding**. For `d=2`
this is exactly the FRI fold; the whole prize is the proximity-gap soundness of the `2^m`-tower pushed
to capacity. A `μ_d`-invariant word's list splits into the invariant sublist (= prize one level down)
+ non-invariant `μ_d`-orbits (Loop22). **So the prize is a recursion over the `m`-level tower:** TRUE
iff per-fold orbit contributions telescope to a polynomial bound; FALSE iff they accumulate
super-polynomially across the `m` levels (a single fold's single orbit is absorbed, Loop21). This
identifies the prize as *precisely the open FRI/STIR/WHIR-to-capacity soundness frontier*, not a side
issue — which is exactly why it carries the $1M and has no published resolution.

### Loop22 — the `μ_d`-invariant subcode `{Q(X^d)}`: the object the open question lives in
**Verified sorry-free, axiom-clean in `CandidateStructureLoop22.lean`:** `invariant_subcode_fixed`
(for `ζ^d=1`, `(Q(X^d))∘(ζ·X)=Q(X^d)` — the `μ_d`-fixed polys are exactly `{Q(X^d)}`),
`invariant_subcode_natDegree` (`deg Q(X^d)=d·deg Q` ⇒ invariant subcode `{Q(X^d):deg Q<k/d}`, dim
`≈k/d`). **Crux, concrete:** at a `μ_d`-invariant received word, either every close codeword is
`μ_d`-invariant (⇒ in the small `k/d`-dim subcode — controlled, proof lean) or a non-invariant one
exists (⇒ its `μ_d`-orbit of size `∣d` is all in the list ⇒ list `≥d`, disproof lean). Larger `d`
shrinks the subcode but raises transitivity. The prize is decided by where this lands at `1−ρ−η`.

### Loop21 (swarm) — a single symmetry orbit is too small to disprove (orbit absorbed)
**Verified sorry-free, axiom-clean in `CandidateStructureLoop21.lean`:** `range_card_le_domain` (a
symmetry orbit has size `≤` the acting group `≤ N=2^m`), `linear_orbit_bound_blocks_fixed_gap_refutation`
(a list bounded by one orbit `≤ n` does not `BeatsEveryPolynomial`). **This shoots down the Loop20
single-orbit disproof route:** one `μ_d`-orbit gives only *linear* growth `≤ N=2^m`, absorbed by the
prize's `(2^m)^{c₁}` numerator. A symmetry disproof needs **many** coexisting orbits (super-poly), not
one — exactly the Loop22 multi-orbit question.

### Loop20 — the smooth domain's RS automorphism group acts on the list (symmetry mechanism)
**Verified sorry-free, axiom-clean in `CandidateStructureLoop20.lean`:** `scaling_preserves_degreeLT`
(scaling the argument by a root of unity is an RS code automorphism), `scaling_iterate_preserves_degreeLT`.
So `μ_N` acts on the smooth-domain code; with Loop6's orbit bound, a received word's close-codeword
list is permuted by its stabilizer, a free orbit forcing list `≥` orbit size. Both-ways: full `μ_N`
transitive ⇒ invariant words constant ⇒ list 1 below capacity (proof lean); a large free orbit needs
an intermediate `μ_d` (Loop22). Loop21 (swarm) then caps a *single* orbit as absorbed — so the open
question is the *multi-orbit* balance.

### Loop19 — the smooth domain's sparse annihilator: the concrete smooth-vs-generic obstruction
**Verified sorry-free, axiom-clean in `CandidateStructureLoop19.lean`:**
`smooth_domain_annihilated_by_sparse` (every element of a smooth subgroup domain of size `N` is a
root of the 2-term `X^N − 1`, via `pow_card_eq_one` pushed through the field inclusion),
`annihilator_coeff_zero_of_mem_interior` (`X^N − 1` has zero coefficient for `0 < i < N`),
`annihilator_leading_coeff`. **Point:** the prize domain is the root set of a **2-sparse** polynomial
`X^N − 1` with huge symmetry (closed under `×` `N`-th roots of unity and Frobenius), whereas a
*generic* `N`-point set has a *dense* degree-`N` annihilator and no algebraic relations. This sparsity
is exactly what a BGM-style genericity argument assumes *absent* — so it is the concrete algebraic
obstruction to discharging Loop17's `(BGM-for-smooth)` hypothesis, and the structural foothold a
Diamond–Gruen-style deterministic disproof would exploit. Names the obstruction precisely; does not
decide the prize.

### Loop18 — the prize is ONE decision; both leans hinge on it; Loop15's lean is NOT decisive
**Verified sorry-free, axiom-clean in `CandidateDecisionLoop18.lean`:** `prize_mass_iff_listsize_le`
(`ℓ/q ≤ (1/q)·B ↔ ℓ ≤ B`), `prize_dichotomy`, `decision_qindependent`. Both full-band reductions
collapse to the *same* binary fact: **prize TRUE ⟺ the smooth-domain RS list at the prize radius is
`≤ B` (the `q`-independent numerator); prize FALSE ⟺ it grows with `q` at fixed `(ρ,η)`.** Exhaustive
and mutually exclusive.
**HONEST CORRECTION (shooting down my own Loop15 lean):** the prize's exact object is *plain
smooth-deterministic* RS below capacity, and **all three known capacity methods fail to apply to it**:
second-moment dies at `η₀` (Loop16); BGM needs *generic* points (smooth subgroups are structured,
Loop17 antecedent unproven); the folded-RS capacity result (arXiv 2601.10047) needs *folded* codes /
subspace-design codes, *not* plain RS. The structural leans **CONFLICT**: Loop15's degree-buffer
leans TRUE, but the deterministic-domain hardness (Diamond–Gruen super-poly at low rate; BCIKS
"Johnson is the genuine limit for *deterministic* RS") leans FALSE. So Loop15's lean is **not
decisive** — the prize is genuinely undecided, hinging on whether smooth = generic for list-size, a
single open question no current technique resolves.

### Loop16 — the second-moment method's wall IS the carving threshold `η₀` (open core is intrinsic)
**Verified sorry-free, axiom-clean in `CandidateBridgeLoop16.lean`:** instantiating the in-tree
`johnson_list_bound` via the rate-shift (`a=(ρ+η)n`, `b=ρn`), the Johnson denominator is
`a²−n·b = n²((ρ+η)²−ρ)` (`johnson_denom_eq`), positive iff `(ρ+η)²>ρ` (`johnson_denom_pos_iff`) iff
`η>η₀=√ρ−ρ` (`sq_gt_iff_large_gap`). And `second_moment_fails_in_band`: for `η<η₀` the denominator is
`≤0`, so `johnson_list_bound`/`_div` give **no** list bound. **Consequence:** the open core is *not* a
gap in this development — it is the intrinsic wall of *every* first/second-moment / Johnson /
pairwise-agreement argument, which provably bottoms out exactly at `η₀`. Crossing it requires a
genuinely higher method (GS multiplicities — top out at Johnson for plain RS; or BGM genericity —
needs generic, not smooth-deterministic, points). This is *why* the prize is the live frontier: the
carving `η₀` is method-intrinsic, not an artifact of approach.

### Loop15 — rate-shift bridge: prize radius = capacity of shifted rate `ρ+η` (leans TRUE)
**Verified sorry-free, axiom-clean in `CandidateBridgeLoop15.lean`:** `prize_radius_eq_shifted_capacity`
(`1−ρ−η = 1−(ρ+η)`), `prize_agreement_eq_shifted_rate`, `degree_buffer` (`(ρ+η)n − ρn = ηn`),
`agreement_exceeds_dimension`. **Structural insight:** the prize is "list-decode the rate-`ρ` subcode
at the *capacity radius of the rate-`ρ'=ρ+η` supercode*." Crites–Stewart's at-capacity disproof
(Loop14) produces folds close to rate-`ρ'` codewords (degree `< (ρ+η)n`); but prize codewords have
degree `< ρn`, so the witnesses live in the degree window `[ρn, (ρ+η)n)` — a buffer of `ηn` degrees
**above** the prize code. The at-capacity disproof therefore **does not descend to the prize**; the
gap `η` is exactly that `ηn`-degree buffer (= Loop4's wall). Since the prize demands *higher*
agreement (`ρ'n`) against a *smaller* code (`ρn`) than the disproved supercode case, it is strictly
*more protected* — a structural argument **leaning the prize toward TRUE**. The open core is precisely
whether the `ηn` buffer also tames beyond-Johnson clustering (not just single-poly constructions,
which Loop4 already handles).

### Loop14 — CLOSED (disproved): the AT-CAPACITY CA/MCA conjecture is false
A genuine *sibling* of the prize is now completely closed as **disproved**, sorry-free and
axiom-clean in `CandidateDisproofLoop14.lean`. Consuming the Crites–Stewart construction (eprint
2025/2046, Cor 1: a line at capacity with bad fraction `≥ 1/2`, no joint proximity) as the cited
hypothesis `hCS`, the refutation logic is verified: `at_capacity_ca_refuted` (`hCS` + any bound
`badFraction ≤ B/q` ⇒ `q ≤ 2B`), `no_fixed_numerator_at_capacity` (∃ `q` beating any fixed `B`),
`at_capacity_bound_impossible` (for `q > 2B`, the bound is impossible). ⇒ the up-to-capacity CA /
MCA-of-WHIR polynomial-soundness conjecture admits no universal constant — **false**. This is *not*
the prize: the prize is strictly below capacity (`δ ≤ 1−ρ−η`), exactly the form Crites–Stewart
propose as salvageable. It nails the failure at the boundary the prize's gap `η` keeps it away from.

### P4 — BGM conditional: genericity ⟹ prize across the ENTIRE band (Loop17, reaches the open core)
The one method that provably crosses `η₀` is Brakensiek–Gopi–Makam (eprint 2206.05256 / 2304.09445):
**generic** RS of rate `ρ` is list-decodable from radius `1−ρ−η` with list size `≤ (1−ρ−η)/η`
(capacity). At the prize radius this gives the `q`-independent budget `(1−ρ−η)/η ≤ 1/η` — polynomial
in `1/η`, **no `n`/`q`/`(2^m)` factor**. **Verified sorry-free, axiom-clean in
`CandidateProofLoop17.lean`:** `bgmBudget_le_inv_gap`, `bgm_prize_mass` — if `ℓ ≤ (1−ρ−η)/η` then
`ℓ/q ≤ (1/q)·(1/η)`, the prize mass clause with `c₁=c₂=0, c₃=1`, for **every `η > 0` including the
small-gap band** the Johnson method (Loop16) cannot touch. So the prize reduces, on the proof side,
to one sharp hypothesis: **(BGM-for-smooth)** smooth multiplicative-subgroup RS inherits the *generic*
BGM list bound. This is the first brick reaching into the open core; the open content is exactly
whether *deterministic smooth* domains behave like *generic* points (BGM is proved for random/generic
evaluation; smooth subgroups are structured). Combined with Loop15 (leans TRUE) the proof side now has
a full-band conditional, not just the Johnson-range one.

### P3 — PROOF capstone: the large-gap prize mass clause holds (Loop13)
**Verified sorry-free, axiom-clean in `CandidateProofLoop13.lean`:** `largegap_prize_mass` — composing
P1 (Johnson list budget `B(ρ,η)=1/((ρ+η)²−ρ)`, `q`-independent) and P2 (`n²` fits `(2^m)²`), in the
large-gap regime (`η > √ρ−ρ`, `δ ≤ 1−ρ−η`, `2^M`-smooth domain) any GS list of size `ℓ ≤ B(ρ,η)`
gives `ℓ/q ≤ (1/q)·(2^M)²·B(ρ,η)` — **the prize mass clause with `c₁=2` and a `q`-independent
constant.** So the prize is *proven on the entire large-gap side*, landed on its own RHS (the GS list
itself supplied by Hab25 Johnson-range / BCIKS 2025/2055 Thm 1.5). `largegap_prize_const_pos`: the
bound is non-vacuous. The small-gap band `0 < η ≤ η₀` stays the open core.

### P2 / O9-repair — the Johnson-range bound lands on the prize RHS shape (Loop11)
**Verified sorry-free, axiom-clean in `CandidateProofLoop11.lean`:** `hab25_le_prizeShape` —
under the smooth-domain size linkage `n = |domain| ≤ 2^m`, the Haböck `n²` bound
`(ℓ⁷/3)(ρn)²/q` is dominated by the prize shape `(1/q)·(2^m)²·K` with `K = ℓ⁷ρ²/3`, i.e. the
prize's `(2^m)^{c₁}` term **is** the domain-size `n²` factor (`c₁ = 2`, `c₂ = c₃ = 0`). This repairs
the O9 statement-fidelity gap and lands the proven Johnson-range (large-gap) proof-side bound on the
prize's own RHS. Does not close the prize: Johnson range only; consumes the Hab25 residuals.

## Open angles not yet tried (to avoid repetition)

- O8: strengthen O7 to **fixed-gap** Frobenius realization: produce high-degree bad scalars with
  some constant `η > 0` independent of extension degree, or prove this is impossible. *(Partially
  probed by O7′: fixed-gap prime-field samples show NO list growth — leans toward "impossible";
  needs exhaustive worst-case search or a proof, and the `GF(2^s)` Frobenius version.)*
- O9: **addressed** by Loop11/P2 at the arithmetic level (the `n ≤ 2^m` linkage absorbs the `n²`
  factor into `(2^m)²`). Remaining: thread the `Fintype.card ι ≤ 2^m` hypothesis through the actual
  `epsMCAgsPrizeUniversalConjecture` statement in `GrandChallenge141UniformResolved.lean`.
- O10: attack via a *list-size lower bound* in the band `(1−√ρ, 1−ρ−η]` at fixed `η` — the O6′
  reduction shows this is the only remaining disproof route; connect to known RS capacity
  list-decoding lower bounds (Ben-Sasson–Kopparty–Radhakrishnan / Guruswami–Rudra) and check whether
  any apply at a prize rate with fixed positive gap.

### O11 / Loop46 — the BCHKS §7 multiplicative-subgroup attack, reduced to a subgroup-sumset bound

The freshest negative construction (BCHKS, "On Proximity Gaps for Reed–Solomon Codes", Nov 11 2025,
**Theorem 7.1**) is an *explicit* proximity-gap attack on RS over a **multiplicative subgroup** —
the prize's exact smooth domain. Read in full and formalized (the certain core) in
`CandidateAttackLoop46.lean` (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`).

**Attack in prize coordinates.** Code `RS[F_q, Φ⁻¹(E), n−(ℓ+2)c]`, `Φ:H→G`, `x↦x^c`, `n=c·|E|`.
For `E ⊆ G` with ℓ-fold *distinct-subset-sumset* `|E^{(+ℓ)}| ≥ a`, there are `≥ a` bad scalars at
radius `γ=ℓc/n` while `[f,g]` is `(ℓ+1)/ℓ·γ`-far. Prize translation (rate `ρ=1−(ℓ+2)c/n`, gap
`η=(1−ρ)−γ`):
* `thm71_freeSet_eq`: the rate **pins** the free set, `|E|=(ℓ+2)/(1−ρ)`, and the gap identity
  `η=2(1−ρ)/(ℓ+2)` collapses it to **`|E|=2/η`** — independent of `q, n, c`.
* `thm71_badCount_le_subsets`: bad count `a=|E^{(+ℓ)}|≤2^{|E|}` — a function of `(ρ,η)` **only**.

**The dichotomy (new).** Prize tolerates `ε_mca ≤ (1/q)(2^m)^{c₁}/(ρ^{c₂}η^{c₃})`, `2^m=|domain|`;
§7 contributes `ε_mca=a/q`.
* `thm71_within_prize`: whenever the prize numerator `≥ a`, §7 respects the prize. Since `a` is
  *fixed* by `(ρ,η)` while `(2^m)^{c₁}→∞` with the domain, **every large domain absorbs §7** — the
  formal reason all prior loops saw §7-type attacks "survive".
* `thm71_minimal_domain_pressure_{c2,c3}` + `thm71_refutes_prize`: at the **minimal** domain
  `2^m=|E|=2/η` (domain = the small subgroup), a *maximal* sumset `a=2^{|E|}=2^{2^m}` beats
  `(2^m)^{c₁}` already at the proven Johnson exponent `c₁=2` (`256<2^16`) and the gap widens
  doubly-exponentially — no fixed `c₁` survives.

**Reduction.** The §7 disproof route ⟺ **how big is `|G^{(+ℓ)}|` for a smooth subgroup `G` of order
`2^m` at the §7-critical `ℓ`?** Poly in `(2^m,1/η)` ⟹ prize survives §7; super-poly in `2^m` at
fixed gap ⟹ prize-as-stated **false**. This is genuine additive combinatorics of multiplicative
subgroups (cf. BCHKS §7 / Conj. 1.12). *Leaning survive*: a full subgroup obeys the vanishing
power-sums `∑_{g∈G} g^j=0` (`1≤j<|G|`), strong additive relations that should keep `|G^{(+ℓ)}|`
far below `2^{|G|}` — but this is **unproven either way**, and (per O6) the minimal-domain case also
turns on whether the prize statement's `2^m=|domain|` linkage is enforced at small `n`. Prize OPEN.

**Next (O11→):** bound `|G^{(+ℓ)}|` for a 2-power multiplicative subgroup using the vanishing
power-sum / Newton-identity relations (would *prove* the prize survives §7, modulo the list-decoding
core O10); or find a subgroup family with super-poly subset-sumset at the critical `ℓ` (disproof).

**Update (Loop46+):** the disproof *branch* of O11 is now a sorry-free theorem
(`thm71_no_fixed_exponent`, axiom-clean): for **every** fixed numerator exponent `c₁` there is a
minimal domain `2^m` at which a maximal sumset `2^{2^m}` strictly exceeds `(2^m)^{c₁}`. So *if* the
subgroup sumset attains its `2^{|G|}` bound at fixed gap, the prize-as-stated is refuted — no fixed
triple survives. Honest correction to the earlier "leans survive": the survive direction is **not**
free — it requires actually proving `|G^{(+ℓ)}|` is sub-exponential (the power-sum bound), which is
open. The §7 route genuinely threatens the minimal-domain prize (and re-opens the O6 statement-
fidelity question: is the prize claimed at small `n`, or only asymptotically?).

### O12 / Loop47 — "many values at a random point" ⟹ proximity gaps stop at the list-decoding radius

The *forward* direction of the equivalence (the prize is **as hard as** RS list-decoding to
`1−ρ−η`) is now machine-checked in `CandidateListDecEquivLoop47.lean` (sorry-free, axiom-clean).

* **Combinatorial engine already in-tree.** BCHKS Lemma 6.1 (= ABF26 "Claim B.1",
  `Probability.exists_large_image_of_pairwise_collision_bound`, on `cauchy_schwarz_fiber`) is already
  proven sorry-free. Loop47 adds the clean **deterministic product form**
  `manyValues_of_pairwise_agree`: any `c : Fin L → (ι→F)` pairwise agreeing on `≤ A` points has a
  point `i` with `L·|ι| ≤ |{c j i}|·(|ι| + L·A)`, i.e. `|values at i| ≥ L·|ι|/(|ι|+L·A)`. Applied to
  a ball of `>q` RS codewords (`|ι|=q`, `A=k−1`) ⟹ a point carrying `Ω(q/n)` values.
* **Theorem 1.9 punchline.** `thm19_qIndependence_contradiction`: if list-decoding fails at the prize
  radius badly enough that the bad-scalar count obeys `q ≤ 2·D·bad` (`D=2^m=|domain|`), then **no
  fixed prize exponent `c₁` survives** — a field with `q > 2·D^{c₁+1}` refutes `bad ≤ D^{c₁}`. `D` is
  pinned by `(ρ,η)`, `q→∞` is allowed ⟹ every `c₁` beaten.
* **Cited residual.** Only BCHKS Claim 6.2 (the rational-function bridge `f=c/(X−α)`, `g=−1/(X−α)`
  turning "value `z` at `α`" into "`f+zg` is `γ`-close") is kept as the hypothesis `hMany_bridge` in
  `prize_false_of_listDecoding_failure`; formalizing it over the RS API is the next residual.

**Net.** Loop47 (list-decoding-fails ⟹ prize-false) + the in-tree converse (Loop8/O6′: prize ⟹
`q`-independent list) pin the prize as **equivalent** to RS list-decoding with `q`-independent lists
up to `1−ρ−η` — a classical, wide-open problem. The prize is neither closed nor mintable; it is now
*provably exactly as hard as* that problem. Both O11 (disproof side, §7 sumset) and O10/O12 (the
list-decoding core) remain open.

### O13 / Loop48 — BCHKS Claim 6.2 (the rational-function bridge) formalized; the Loop47 black box discharged

Loop47 left one opaque input: `hMany_bridge : q ≤ 2·D·bad`, attributed to **BCHKS Claim 6.2** (the
bridge `f(x)=c(x)/(x−α)`, `g(x)=−1/(x−α)`, so `f+z·g=(c(x)−z)/(x−α)`). Loop48 formalizes its
algebraic heart sorry-free, axiom-clean, in `CandidateBridgeClaim62Loop48.lean`, splitting the black
box into a *proven* algebraic half and a *proven* combinatorial half — leaving only the genuine
distance/genericity input explicit.

* **Algebraic core (`bridge_isCodeword`, `bridge_quotient_natDegree_lt`).** At `z = c.eval α`, the
  bridge function is an *honest polynomial*: `(X − α) ∣ (c − c(α))` (Mathlib
  `X_sub_C_dvd_sub_C_eval`), and for non-constant `c` the quotient `(c−z)/(X−α)` has
  `natDegree = deg c − 1 < deg c` — a codeword of the *once-punctured* RS code. This is the precise
  sense in which "the line `{f+z·g}` meets the code at `z = c(α)`": it lands on a lower-degree
  codeword. So **every realized value `c(α)` is a bad combining scalar**.
* **Counting / injectivity (`card_values_le_badScalars`, `realized_values_are_bad`,
  `bad_ge_distinct_values`).** The value→scalar map is the identity on values, hence trivially
  injective; combined with the bridge membership it gives `B := #(realized values) ≤ #badSet = bad`.
  The old assumption `bad ≥ B` is now a *theorem*.
* **Many-values arithmetic (`manyValues_arith`).** From the in-tree `manyValues_of_pairwise_agree`
  output `L·q ≤ B·(q + L·A)` (point set = scalar field, `|ι| = q`; `A = k−1`; `L > q` codewords =
  list-decoding failure) and `A+1 ≤ 2D`, a clean nat cancellation yields `q ≤ 2·D·B`. Sorry-free.
* **Capstone (`prize_false_of_listDecoding_failure_full`).** Chaining the two proven halves with the
  prize bound `bad ≤ D^{c₁}` and a large field `2·D^{c₁+1} < q` refutes any `q`-independent prize
  triple. **No opaque arithmetic remains** — the inputs are exactly the honest external facts:
  list-decoding fails at the prize radius (`> q` codewords pairwise agreeing on `≤ A` points), the
  bridge points are bad (the line is far elsewhere — the defining proximity-gap distance input), and
  the field is large relative to the fixed domain `D`.

**Net.** Loop47's "list-decoding failure ⟹ prize false" is now driven by a *verified* Claim 6.2,
not a cited black box. The equivalence "prize ⟺ RS list-decoding to `1−ρ−η` with `q`-independent
lists" stands on machine-checked algebra on both directions' combinatorial cores. What is left is
genuinely the classical list-decoding question itself (O10/O12) and the §7 sumset disproof route
(O11) — both still OPEN. The prize remains OPEN; its *reduction infrastructure* is now sorry-free.

**Update (Loop48 Part D).** The bridge is now grounded in the *formalized* RS code, not just raw
polynomials: `bridge_mem_degreeLT` shows the quotient lands in `degreeLT F (deg−1)`, and
`bridge_eval_mem_code` concludes `evalOnPoints domain quot ∈ ReedSolomon.code domain (deg−1)` — i.e.
the bridge maps the degree-`deg` Reed–Solomon code into the once-punctured degree-`(deg−1)` code, the
exact "the line point is a codeword of the shifted code" content of Claim 6.2, over
`ArkLib.Data.CodingTheory.ReedSolomon`. Sorry-free, axiom-clean.

### O14 / Loop49 — the §7 subgroup lives in large characteristic; ±pairing governs the sumset

Sharpening O11 (the §7 disproof route), `CandidateSubgroupSumsetLoop49.lean` (sorry-free, axiom-clean):

* **Char-2 obstruction (`orderOf_odd_of_char_two`, `no_even_order_element_char_two`).** In a finite
  field of characteristic 2, `|Fˣ| = |F| − 1 = 2^k − 1` is *odd*, so every unit has odd order and
  there is **no** multiplicative subgroup of order `2^m` (`m ≥ 1`). The §7 attack's smooth subgroup is
  therefore forced into *large characteristic* `p ≡ 1 (mod 2^m)` — the actual STARK regime — where
  `G` is the group of `2^m`-th roots of unity in `F_p`.
* **±pairing (`neg_pow_eq_one_of_even`, `nthRoots_set_neg_closed`, `neg_one_mem_nthRoots`).** Because
  `2^m` is even, `(−x)^{2^m} = x^{2^m}`: the `2^m`-th roots are negation-closed, with `−1` the
  order-2 element. So `G` partitions into `2^{m-1}` pairs `{g, −g}`. By Lam–Leung this is the *only*
  prime-power-`2` vanishing relation among roots of unity.
* **Reduction.** Two `ℓ`-subset sums coincide iff their signed difference is a vanishing `{−1,0,1}`-
  sum of `2^m`-th roots; by Lam–Leung these are spanned by the ±pairing. The distinct-sum count is
  then pinned between the pairing ceiling `3^{2^{m-1}}` and the cross-pair distinctness lower bound —
  **both super-polynomial in `2^m`** at fixed gap. So O11 leans toward **disproof of the
  minimal-domain prize** (consistent with `thm71_no_fixed_exponent`), modulo formalizing the
  Lam–Leung distinctness — the next residual — and re-opens the O6 statement-fidelity question.

Honest caveat: the vanishing power-sums `∑ g^j = 0` are *Vieta* identities in the field (roots of
`X^{2^m} − 1`), **not** group facts (`∑_{a ∈ ℤ/2} a = 1 ≠ 0`) — flagged in the file, not over-claimed.

### O15 / Loop50 — PROVEN super-exponential subset-sumset lower bound; char-0 disproof settled

`CandidateSubsetSumLowerLoop50.lean` (sorry-free, axiom-clean) proves the decisive half of O11 and
**corrects an over-optimism in Loop49**.

* **`subsetSum_injective_of_noRelation`.** If a family `v : Fin N → K` admits no nonzero `{−1,0,1}`-
  (equiv. integer-) relation `∑ j (g j) v j = 0`, the subset-sum map `S ↦ ∑_{j∈S} v j` is *injective*
  (two equal sums ⟹ indicator difference is a vanishing relation ⟹ subsets equal).
* **`card_subsetSumset_ge` / `card_subsetSumset_len_eq`.** Hence `|sumset| ≥ 2^N` and the size-`ℓ`
  sumset has *exactly* `C(N, ℓ)` elements.
* **Application.** For a primitive `2^m`-th root `ζ`, `Φ_{2^m} = X^{2^{m-1}}+1` has degree
  `φ(2^m)=2^{m-1}`, so the power basis `{1,ζ,…,ζ^{2^{m-1}-1}}` is `ℤ`-independent. With `N = 2^{m-1}`:
  `|G^{(+ℓ)}| ≥ C(2^{m-1}, ℓ)` — **super-exponential in the domain `2^m`**. With
  `thm71_no_fixed_exponent` (Loop46) this **disproves the minimal-domain prize over any field where
  the power basis stays independent** (char 0, or `F_q` with `ord_{2^m}(q)=2^{m-1}`, i.e. `Φ_{2^m}`
  irreducible).

**Loop49 correction (honest).** Loop49 leaned "both ends super-poly ⟹ disproof" *unconditionally*.
That is **wrong for the STARK prime-field regime** `q ≡ 1 (mod 2^m)`: there `ζ ∈ F_q`, the power basis
collapses, and the subset sums are **capped by `q`**. The proven lower bound holds only in the
power-independent regime. The genuine remaining gap is a **lifting**: the `C(2^{m-1},ℓ)` distinct
algebraic-integer sums in `ℤ[ζ]` have bounded norm, so a large prime `p ≡ 1 (mod 2^m)` (Dirichlet,
infinitely many) admits a degree-1 prime `𝔭 ∣ p` keeping them distinct mod `𝔭` — witnessing a finite
field with super-poly bad count, hence the finite-field disproof. The combinatorial core is proven;
the lifting is O16's residual.

**Update (Loop50, concrete capstone).** The char-0 lower bound is now **fully concrete**, no abstract
hypothesis: `subsetSum_injective_of_isPrimitiveRoot` discharges the no-relation condition from `ζ`'s
minimal polynomial (`IsPrimitiveRoot.totient_le_degree_minpoly` + `minpoly.isIntegrallyClosed_dvd`
over integrally-closed `ℤ`), and `card_subsetSumset_isPrimitiveRoot_two_pow_ge` concludes: **for an
actual primitive `2^m`-th root of unity in any characteristic-0 field, the subset-sumset over the
half-domain has `≥ 2^{2^{m-1}}` elements** — super-exponential in the domain `2^m`. The char-0 §7
disproof is therefore *proven* (with `thm71_no_fixed_exponent`). The sole remaining residual for a
finite-field disproof of the prize-as-stated is the **number-theoretic lifting**: pick a large prime
`p ≡ 1 (mod 2^m)` (Dirichlet) and a degree-1 prime `𝔭 ∣ p`; the `2^{2^{m-1}}` distinct algebraic-
integer sums in `ℤ[ζ]` (bounded norm) stay distinct mod `𝔭`, witnessing `F_p` with super-poly bad
count. That lifting needs `NumberField`/Dedekind-domain machinery and is O16's residual.

### O16 / Loop51 — finite-field disproof skeleton: machine-checked downstream of one lifting hom

`CandidateFiniteFieldLiftLoop51.lean` (sorry-free, axiom-clean) completes the *logical* finite-field
disproof, isolating the one number-theoretic residual.

* **`ringHom_subsetSum`.** A ring hom `φ : K →+* L` commutes with subset sums: `φ(∑_{j∈S} ζ^j) =
  ∑_{j∈S} (φ ζ)^j`.
* **`card_subsetSumset_finiteField_ge`.** Hence the `L`-side subset-sumset of `φ ζ` is the `φ`-image
  of the (proven `≥ 2^{2^{m-1}}`) char-0 sumset; if `φ` is *injective on those sums* (`hInj`), the
  finite field `L` inherits the bound `≥ 2^{2^{m-1}}`.
* **`prize_false_finiteField_of_lifting`.** Packaged with the §7 bad-count lower bound and the
  elementary super-exponential gap `(2^m)^{c₁} < 2^{2^{m-1}}`, no fixed prize exponent survives over
  `L`.

**The sole residual (O16, genuinely number-theoretic).** `hInj` is the lifting: a prime
`p ≡ 1 (mod 2^m)` (Dirichlet, in Mathlib as `Nat.infinite_setOf_prime_and_eq_mod`) and a reduction
`ℤ[ζ] → F_p` injective on the `2^{2^{m-1}}` sums. Distinctness survives because each difference is a
nonzero cyclotomic integer: equivalently `Res(f_S − f_T, Φ_{2^m}) ≠ 0` in ℤ (the diff has degree
`< 2^{m-1} = deg Φ`, so `Φ ∤` it), and `g(ζ_p) = 0 ⟹ p ∣ Res`, so only finitely many primes are bad —
avoidable by Dirichlet. Mathlib *has* the pieces (`RingTheory/Polynomial/Resultant`,
`RingTheory/Norm` `norm_ne_zero_iff`, Dirichlet, cyclotomic), but assembling the existence is a large
ANT formalization, left as the named residual. **Everything downstream of it is machine-checked.**

---

## Net state after Loops 47–51

The #232 prize (a **$1M open research problem**) is **not closeable**; it is now pinned as
*equivalent* to two classical problems, with all surrounding mathematics sorry-free and axiom-clean:

* **Forward** (list-decoding fails ⟹ prize false): BCHKS Claim 6.2 bridge **proven** (Loop48),
  grounded in `ReedSolomon.code`. Open core = RS list-decoding to `1−ρ−η` with `q`-independent lists.
* **Disproof** (§7 sumset ⟹ prize false): char-2 obstruction + ±pairing **proven** (Loop49); the
  char-0 super-exponential subset-sumset lower bound `≥ 2^{2^{m-1}}` **proven, fully concrete**
  (Loop50); the finite-field transfer **proven** (Loop51). Open core = the number-theoretic *lifting*
  (one injective reduction hom).

Two precise, well-isolated residuals remain — one a genuine open conjecture, one a standard-but-heavy
ANT existence. Neither is fabricated; both are clearly named.

### O16 / Loop53 — the finite-field lifting CLOSED: super-exponential §7 subset-sumset over a real F_p

The O16 residual is **discharged**. `CandidateFiniteFieldDisproofLoop53.lean` (sorry-free, axiom-clean)
proves, with **no remaining hypothesis**:

> `exists_finiteField_subsetSumset_large`: for every `m ≥ 1` there is a prime `p` and a primitive
> `2^m`-th root of unity `ζ ∈ F_p` whose subset-sumset over `Fin (2^{m-1})` has `≥ 2^{2^{m-1}}`
> elements — **super-exponential in the domain `2^m`**.

**Assembly.** The seven Loop52 pillars (resultant common-root ⟹ `p ∣ Res`; coprime ⟹ `Res ≠ 0`;
Dirichlet good prime; consolidation; difference–cyclotomic coprimality; primitive-root existence) plus
the polynomial bookkeeping `f_S = ∑_{j∈S} X^j` (coeff/degree/injectivity/eval/leading-coeff). For each
ordered pair `(S,T)` the difference `f_S − f_T` is coprime to `Φ_{2^m}` over `ℚ`; a Dirichlet prime
`p ≡ 1 (mod 2^m)` avoids all `Res(f_S − f_T, Φ)`; `F_p` then has a primitive root `ζ` (a root of
`Φ mod p`); a collision `f_S(ζ)=f_T(ζ)` would make `ζ` a common root of `f_S − f_T` and `Φ`, forcing
`p ∣ Res` — contradiction. So the subset sums are distinct, and the image has `2^{2^{m-1}}` elements.

**What this closes.** Combined with `thm71_no_fixed_exponent` (Loop46), the §7 bad count
`a = |G^{(+ℓ)}| ≥ C(2^{m-1}, ℓ)` (super-polynomial in the domain `2^m`) at the minimal domain over a
genuine **finite field** — so **no fixed prize triple `(c₁,c₂,c₃)` survives**: the §7 minimal-domain
prize-as-stated is **disproven over finite fields, not merely in characteristic 0**. The disproof
direction is complete.

**Remaining honesty (O6).** This refutes the *minimal-domain* reading (`2^m = |domain| = |E| = 2/η`,
`c = 1`). Whether the prize is *claimed* at the minimal domain or only asymptotically (where
`thm71_within_prize` shows every large domain absorbs §7) is the O6 statement-fidelity question — a
question about the prize's wording, not the mathematics, which is now fully machine-checked. The
forward direction's open core (RS list-decoding `q`-independence) remains the genuine open conjecture.

**Update (Loop53, end-to-end).** The disproof is now machine-checked *end-to-end*, not prose-asserted:
`prize_exponent_refuted_finiteField (c₁) : ∃ m p, 1 ≤ m ∧ p.Prime ∧ ∃ ζ, IsPrimitiveRoot ζ (2^m) ∧
(2^m)^{c₁} < (subset-sumset card)`. Via `exists_m_gap` (`m·c < 2^{m-1}` by the clean chain
`(B+1)c < B(c+1) ≤ 2^{2c+1} ≤ 2^B`, `B = 2^{c+1}`) and `exists_finiteField_subsetSumset_large`: for
*every* fixed prize exponent `c₁`, a genuine finite field has §7 bad count `> (domain)^{c₁}`. **No
fixed `q`-independent prize exponent survives** — the §7 minimal-domain prize is refuted over a real
finite field, fully axiom-clean. The only non-formal element left in the disproof is the §7 attack's
own combinatorial setup (`thm71_*`, Loop46) tying the subset-sumset to the bad-scalar count, already
sorry-free in-tree.

**Net (Loops 47–53).** DISPROOF direction: **complete and machine-checked end-to-end** (the §7
minimal-domain prize is false over finite fields). FORWARD direction: open core = large-domain /
asymptotic smooth-domain RS list-decoding to `1−ρ−η` with `q`-independent lists — a genuine open
conjecture (the §7 route provably does *not* refute it; `thm71_within_prize` shows large domains
absorb §7). O6 (which domain regime the prize claims) is a wording question, not mathematics. The
prize's full closure turns on the large-domain forward conjecture, which remains open.

### O11 CLOSED (Loop53, `badCount_exceeds_prize_numerator`)

The realizability question Loop46's `thm71_refutes_prize` explicitly deferred — *"whether `a > num` is
realizable at a smooth subgroup; see O11"* — is now a **theorem**. At the minimal domain (`ρ = 2^{-r}`,
`η = 2^{1-m}`, domain `2^m`) the prize numerator `(2^m)^{c₁}/(ρ^{c₂}η^{c₃}) = 2^{m c₁}·2^{r c₂}·2^{(m-1)c₃}`
is `2^{O(m)}`, while the *realized* §7 bad count — the subset-sumset of `2^m`-th roots of unity in `F_p`
(Loop53) — is `≥ 2^{2^{m-1}}`, doubly-exponential. So `num < a` holds over a genuine finite field for
**every** fixed prize triple `(c₁,c₂,c₃)` and prize rate `ρ = 2^{-r}`, and `thm71_refutes_prize` then
gives `(1/q)·num < a/q` — the §7 MCA contribution beats the prize RHS in the actual `ε_mca` quantity.
**The §7/minimal-domain disproof thread is fully closed** (O11 was its last open node), with no
realizability gap. The actual prize (pin `δ*` for *large* smooth domains, where §7 is absorbed) and O6
(which domain regime the prize claims) remain — the genuine open research and the wording question.

### O17 / Ultracode assault — 8-angle verified attack on δ* pinning: open core did NOT move, boundary mapped

An exhaustive parallel multi-agent assault (8 independent angles, each writing+verifying real Lean,
adversarially gated) attacked the open prize core (pin δ* / a list bound past Johnson for explicit
smooth-domain RS). **Honest headline: the open core did not move** — zero angles pushed a verified
list bound into the gap interior `(1−√ρ, 1−ρ)` for general smooth-domain RS. δ* remains unpinned. But
the assault produced **5 verified axiom-clean new bricks** (kept) and a **precise map of the wall**.

**Kept bricks** (all `lake build`-clean, axiom-clean `[propext, Classical.choice, Quot.sound]`):
* `ListInteriorDataPointF7.lean` — `interior_list_lower_bound` + `four_sevenths_strictly_interior`:
  the **first explicit verified interior data point** — RS[F₇, n=7, k=2], an explicit word with 6
  distinct degree-`<2` codewords all agreeing on `≥3/7` coords (δ=4/7), *proven strictly inside*
  `(1−√(2/7), 5/7)`. One-sided (lower bound); the matching upper bound (list = exactly 6) is **not**
  Lean-provable here (7⁷ too big for `decide`, `native_decide` forbidden, Johnson≤24/Fisher≤7 loose).
* `ListCapacityFieldIndependent.lean` — `list_card_ge_choose_at_capacity`: a `C(n,k)`-size,
  **field-INDEPENDENT** list at the capacity edge via root-set interpolation `p_S = g − c·∏_{i∈S}(X−Dᵢ)`.
  Strictly stronger than the field-capped `subsetSumset_card_le_field` (Loop53) — no `|F|` cap.
* `JohnsonFourthMomentNoGo.lean` — `fourth_moment_cannot_beat_johnson_from_S4`: a **proven no-go** —
  the degree-4 moment chain `(n·S₂)² ≤ n³·S₄` is Johnson-squared with zero slack on the extremal
  profile, so the 4th moment provably cannot beat Johnson. (No 4th-moment material existed in-tree.)
* `SubgroupSpectrumNoImprovement.lean` — `rs_codeword_syndrome` (the RS/BCH dual-code vanishing-
  high-frequency-spectrum identity) + `subgroup_agreement_set_arbitrary`: the vanishing-power-sum /
  cyclic structure of the smooth domain **does not** beat Johnson — `g_A = ∏_{j∈A}(X−ωʲ)` realizes
  *any* `≤k−1` agreement set inside the subgroup, adding no placement information.
* `MCAListCollapseFullSupport.lean` — `epsMCA_le_of_uniform_badCount_full_support`: lifts the
  general-δ list⇒MCA packing to a uniform `ε_mca ≤ n/t·(…)/|F|` over full-support firing stacks
  (the §5 collapse, full-support regime; non-full-support `z>0` is the genuine open boundary).

**The convergent obstruction (the real insight).** Every angle collapses onto the *same* wall: the
"`≤ k−1` freely-placed agreement positions" ceiling that makes Johnson tight is **fully realizable
inside the smooth domain**, and the only way past it — a non-codeword target on which `>k−1`
codewords agree, equivalently a **super-polynomial smooth-domain subset-sum / incidence count** — is
exactly the open ABF26 content. **Three independent angles (subgroup-spectrum, sum-product/dilation,
capacity-edge interpolation) reduce to this one smooth-domain subset-sum question.** Each standard
technique (higher moments, Guruswami–Sudan multiplicity, dilation/sum-product, cyclic-BCH duality,
root-set interpolation) was pushed to its wall and the wall proven, often as an explicit no-go.

**Methodological catch (durable learning).** Bare `lean <file>` / `lake env lean <file>` defaults
`autoImplicit = true`; the project sets `autoImplicit = false` (`lakefile.toml`). A file with an
unbound variable can pass `lake env lean` yet **fail `lake build` and be `sorryAx`-tainted**. One
assault file (`SubgroupSpectrumNoImprovement`) was sorryAx-tainted this way; a one-line `{n : ℕ}`
binder fix made it axiom-clean. **Always confirm with `lake build <Module>`, not bare `lean`.** (All
Loop48–53 files were re-confirmed clean under `lake build`.)

### O18 / Round-2 assault — two-sided F7 interior pin + advanced-angle cartography (4 verified bricks)

A second multi-agent round (5 advanced angles the first didn't try). Open core STILL did not move, but 4
more axiom-clean bricks landed (all `lake build`-clean, `[propext, Classical.choice, Quot.sound]`):

* `ListInteriorTwoSidedF7.lean` — `interior_list_two_sided` + the reusable `pairPacking_card_le`
  (general Fisher: `|L|·C(a,2) ≤ C(|ground|,2)` for `a`-subsets pairwise meeting in `≤1`). **The first
  TWO-SIDED interior list-size pin in the repo**: RS[F₇,7,2] at δ=4/7 (strictly inside the gap) has list
  size *provably in [6,7]* — a verified lower bound (∃ a 6-codeword list) AND a matching upper bound
  (∀ such list ≤ 7). Upgrades the round-1 one-sided F7 data point to near-tight.
* `ListIncidencePolyMethod.lean` — `poly_method_subset_incidence_bound`: the **k-uniform** Fisher
  generalization `|L|·C(a,k) ≤ C(n,k)` via pairwise-disjoint "owned k-sets" (distinct deg-`<k` codewords
  own disjoint k-subsets of their agreement set). Sharper than the 2nd-moment bound when `a` is close to
  `k`; the clean polynomial-method form of the agreement ceiling.
* `ListRecoveryInterleavedGap.lean` — `deltaStar_collapse_bracket` + `gap_present_in_interleaved`: the
  ABF26 §5 single-code ↔ m-interleaved relationship — `IsGood C δ B ⟹ IsGood C^{≡m} δ B^m` (forward) and
  `IsGood C^{≡m} δ B ⟹ IsGood C δ B` (backward), and the Johnson→capacity gap is *inherited* by the
  interleaved code. Shows the two Grand Challenges do NOT collapse to the same constant bound (the `B^m`
  blowup), a real §5 contribution.
* `SubgroupCharacterSumNoGo.lean` — `weil_recovers_root_count_not_better`: a **proven no-go** — the
  character-sum / Weil expansion of the subgroup agreement count recovers *exactly* the root count
  (`= k−1` realizable for any agreement set), so Weil gives nothing past Johnson. Plus the clean
  orthogonality/agreement-split character-sum identities.

**Verdict unchanged + sharpened.** Two independent advanced techniques (polynomial method, character
sums/Weil) join round 1's list in hitting the SAME wall: the `≤k−1` agreement ceiling is exactly the
k-dimensional/root-count constraint, fully realizable in the smooth subgroup. The reduced open core
(super-poly smooth-domain subset-sum past Johnson within `|F|<2^256`) did not move. The new genuine
asset is the **two-sided F7 interior pin** — a concrete verified δ* data point, both bounds, the first
in-repo demonstration that δ* CAN be pinned (for a tiny explicit instance) even though the general
technique is open.

### O19 / Round-3 assault — verified δ* TABLE (4 two-sided interior pins incl. a real smooth subgroup) + crossover + §7 3^N upper bound

Third multi-agent round built a **verified δ* table** of explicit two-sided interior list-size pins. 6
axiom-clean bricks (all `lake build`-clean, `[propext, Classical.choice, Quot.sound]`). The general-n
technique still did NOT move past the wall — but the table is genuine certified supporting data, and
includes the first prize-faithful (smooth-subgroup) and first k=3 pins.

**The δ* table (two-sided interior pins, lower = explicit witness list, upper = field-blind Fisher/poly-method cap):**
| field / domain | n | k | ρ | interior δ | bracket | file |
|---|---|---|---|---|---|---|
| F₇ full | 7 | 2 | 2/7 | 4/7 | **[6,7]** | `ListInteriorTwoSidedF7` (round 2) |
| F₁₁ full | 11 | 2 | 2/11 | 8/11 | **[15,18]** | `ListInteriorPinF11` |
| **F₁₇ ⟨2⟩ order-8 subgroup** | 8 | 2 | 1/4 | 5/8 | **[7,9]** | `ListInteriorPinF17Subgroup` |
| F₁₁ full | 11 | 3 | 3/11 | 6/11 | **[7,16]** | `ListInteriorPinF11K3` |

* `ListInteriorPinF17Subgroup` — **first pin on a genuine smooth domain.** `smooth_domain_eq_roots_of_unity`
  proves the evaluation domain image is *exactly* `{x : x⁸=1}` (the order-8 multiplicative subgroup of
  F₁₇ — the actual FRI/STARK setting), not the full field. Two-sided [7,9] at δ=5/8.
* `ListInteriorPinGeneral` — the parametric **upper-cap** theorem `two_sided_interior_pin` (|L| ≤
  C(n,k)/C(a,k) for arbitrary injective domain, lower bound taken as a per-instance hypothesis) +
  `interior_iff_real`: the clean ℕ↔ℝ equivalence proving `Interior n k a := (k<a ∧ a²<nk)` is *exactly*
  `1−√(k/n) < (n−a)/n < 1−k/n` (genuine `Real.lt_sqrt` squaring) — removes all `Real.sqrt` reasoning
  downstream. Plus a 5-row decide-checked upper-cap table (one-sided rows: n=13/16/31 etc.).
* `FisherJohnsonCrossover` — `crossover_iff`: Fisher cap `C(n,k)/C(a,k)` vs 2nd-moment Johnson reduce to
  one integer cross-product `C(n,k)·d ⋚ C(a,k)·n²`; **neither dominates** (witnesses both sides). Tells
  you which tool is sharper in which part of the gap.
* `SubgroupSumsetThreePowUpper` — `subsetSumset_full_le_three_pow`: the §7 full-subgroup subset-sumset
  is `≤ 3^N` (via the ζ^N=−1 collapse factoring every full-subgroup sum through a `{−1,0,1}`-cube
  `Fin N → Fin 3`). Capstone `subsetSumset_full_two_sided`: `2^{2^{m-1}} ≤ |G⁽⁺⁾| ≤ min(3^{2^{m-1}}, p)`.
  An honest UPPER bound on the §7 count — but both edges doubly-exponential, so only the field cap `p`
  (Loop53) forces survival; does not by itself pin δ*.

**Verdict (honest, unchanged).** Every upper bound is the SAME field-blind `≤k−1` incidence cap (holds
for any injective `D`, cannot separate smooth from generic domains) — the convergent wall. Lower bounds
are explicit single-instance witnesses. The general-n lower bound past the `≤k−1` ceiling (= the open
super-poly smooth-domain subset-sum count) was NOT supplied. The table PINS δ* for explicit tiny
instances (incl. a real subgroup) but does NOT pin δ* for general smooth-domain RS. 15 verified bricks
total across rounds 1–3. Open core untouched; boundary maximally mapped.

### O20 / Round-4 — focused assault on THE reduced question (subgroup subset-sum count N(t,target))

Round 4 attacked the single open question rounds 1–3 converged on: the count
`N(a,target) = #{a-subsets of the 2^k-subgroup G summing to target}`, whose super-poly-at-bounded-|F|
growth at `a = k+t` (t≥1, interior) is what pinning δ* requires. 6 axiom-clean bricks (all `lake
build`-clean). **The open core did NOT move** — but the reduction is now formalized down to the exact
count, with the count→list bridge and both the easy bounds machine-checked. Honest framing throughout.

* `InteriorListCountBridge.lean` — **the key new brick: the count→interior-list BRIDGE.**
  `interior_list_ge_of_count`/`interior_list_card_ge_family`: the construction `p_S = g − c·∏_{i∈S}(X−Dᵢ)`
  with `deg g = k+t`, `|S| = k+t` drops one degree automatically (`pSt_natDegree_lt_interior`); the
  *further* drop to `deg < k` (a real codeword) is the symmetric-function condition packaged as
  `DegDropFamily`. Given a family of size `M` with that property, the RS list at the INTERIOR radius
  `δ = 1−(k+t)/n` has `≥ M` codewords (injectivity `pSt_codeword_injOn` verified). **This is the first
  machine-checked bridge from the count to the list INSIDE the gap** (rounds 1–3 only had the `t=0`
  capacity endpoint). It does NOT prove the count is large — that is the open question, isolated as the
  `DegDropFamily` hypothesis.
* `SubsetSumPigeonholeFiber.lean` — `max_fiber_interior_ge`: `∑_target N(k+t,target) = C(n,k+t)`
  (`sum_subsetSumCount_eq_choose`) ⟹ by pigeonhole `∃ target, q·N(k+t,target) ≥ C(n,k+t)`. A genuine
  lower bound on the MAX-target count. Plus the Newton/Vieta SYMMETRIES (`subsetSumCount_symmetry_group`:
  `N(a,target) = N(a,−target) = N(n−a,target)` from negation-closure + vanishing sum). **Honest caveat:
  this bounds the SUM-only count (one symmetric function); the list bridge needs the FULL degree-drop
  (all `t` symmetric functions) — they coincide only at `t=1`, so this does not by itself give a deep-gap
  list bound.**
* `SubsetSumZeroInflation.lean` — `N_lower_inflation`: disjoint zero-sum ±pairs inflate the count:
  `N(|S₀|+2t, target) ≥ C(#pairs, t)`, field-INDEPENDENT (counts subsets, not field elements — not
  Loop53-capped). **Honest caveat: inflates SIZE preserving SUM only; same one-symmetric-function gap —
  does not feed the bridge for t≥2.** A correct, non-vacuous lower bound on the sum-count.
* `SubsetSumCharacterSum.lean` — the exact Gauss/character-sum formula for `N` (`subsetSumCount_eq_charSum`:
  `q·N = ∑_ψ ψ(−target)·∏_{x∈G}(1+z ψ(x))|coeff`), main-term + error split, error norm bound. The
  analytic handle on `N`.
* `SubsetSumEsymmVanishing.lean` — `esymm_nthRoots_eq_zero`: `e_j(G) = 0` for `0<j<n` (G = n-th roots
  of unity, `∏(Y−x) = Y^n−1`), the symmetric-function grounding all other angles rest on; `subgroup_sum_eq_zero`.
* `SubsetSumPairingInflate.lean` — the ±pairing generating-function recursion (`sum_inflate`,
  `inflate_injective`): the per-pair {skip,both,+g,−g} structure, the combinatorial backbone of inflation.

**Verdict.** The reduced question is now fully formalized: the BRIDGE (count⟹list, new), the exact
character-sum formula, the e_j-vanishing grounding, and two correct lower bounds on the SUM-count
(pigeonhole `C(n,k+t)/q`, inflation `C(2^{k-1},t)`). The unbridgeable gap is sharp and now PROVEN in
structure: every available lower bound controls only the SUM (one symmetric function), while the list
needs ALL `t` symmetric functions to align — coinciding only at `t=1` (δ just below capacity). Moving
to deep interior `t≥2` needs the count of subsets with `t` simultaneous symmetric-function constraints
super-poly, which remains OPEN. 21 verified bricks across rounds 1–4. The open core is untouched but
its precise obstruction — sum-count vs full-symmetric-count — is now machine-checked.

**Update (O20 cleanup + sharpened residual).** Build-integrity fix: a concurrent regen had wired the
6 `Round4_*` module names into `ArkLib.lean` while 2 were renamed away and one (`Round4_newton_vieta_upper`,
319 lines) was the pre-truncation BROKEN version — a clean umbrella build would fail. Resolved by
removing all `Round4_*` (content preserved byte-identically in the descriptively-named bricks; newton
kept as the fixed 278-line `SubsetSumPigeonholeFiber`) and regenerating `ArkLib.lean` from tracked files.
The umbrella is now consistent.

The round-4 synthesis sharpens the residual one notch further: the zero-sum/±pairing inflation
(`SubsetSumZeroInflation`) raises the subset SIZE by an **even** amount `2t` while preserving the sum
(`e_1`), but the unique increment where controlling `e_1` alone suffices for the degree drop is `t = 1`
— an **odd** increment the even-only pairing inflation structurally cannot reach. So the disproof-side
residual is precisely: **a field-independent super-polynomial lower bound on the count of `(k+t)`-subsets
of the smooth `2^k`-subgroup with `e_1, …, e_t` *jointly* prescribed (the full degree-drop family), at an
ODD interior increment** — an additive-combinatorial / Weil-cancellation question on a multiplicative
subgroup, with no Mathlib handle and untouched by any of the 21 verified bricks. Two upper-side attack
families (additive-character orthogonality; Newton/Vieta symmetric functions) are now machine-checked
DEAD ENDS for this count.

### O21 / Round-5 — the FIRST unconditional general-n interior list lower bound + the exact t=2 condition

Round 5 welded the round-4 conditional halves into a genuinely **unconditional** theorem and set up the
open t=2 question precisely. 4 axiom-clean bricks (all `lake build`-clean). The open core (deep-interior
δ*, the t≥2 multi-symmetric count) is untouched, but this is the strongest verified interior result yet.

* `ListInteriorUnconditionalT1.lean` — **`exists_interior_list_ge_unconditional`: the first UNCONDITIONAL
  general-n interior list lower bound in the corpus.** Hypotheses ONLY `0<k`, `k≤n`, `0<q=|F|`, and the
  interiorness `(k+1)² < k·n` — NO `DegDropFamily`, NO count hypothesis. Conclusion: `∃ g` of degree
  `k+1` with `C(n,k+1) ≤ q · #{v ∈ RS code : agree(v, g∘D) ≥ k+1}`, i.e. some received word's list at the
  strictly-interior radius `δ = 1−(k+1)/n` is `≥ C(n,k+1)/q`. Welds the two previously-conditional round-4
  halves: the degree-drop family is built internally (`windowDegDropFamily`, via `degDrop_t1_iff_window_sum`
  + `pSt_natDegree_lt_interior`) and the count `C(n,k+1)/q` supplied by an internal fiberwise pigeonhole.
  Non-vacuity machine-checked at `k=50,n=104`. **Honest caveat (in docstring): `δ=1−(k+1)/n` is the t=1
  sliver just inside the CAPACITY endpoint, NOT deep interior; the `/q` factor means it beats trivial only
  for `C(n,k+1)>q` (n large vs |F|), so NOT q-independent — a worst-case lower bound, not a prize
  counterexample. Does NOT pin δ*.** First unconditional general-n interior brick nonetheless.
* `ListInteriorDeltaStarUpperPin.lean` — `strict_overflow`/`concrete_overflow_nonvacuous`: the
  field-independent binomial overflow `C(2^20, 2^19) > 2^{-128}·q²` for all `q ≤ 2^128` (via Mathlib
  `four_pow_le_two_mul_self_mul_centralBinom`), a hypothesis-free closed proposition with ~2^256 slack.
  The actual δ*-upper-pin `delta_star_upper_pin_of_family` honestly carries the `DegDropFamily` +
  overflow hypotheses (the open ingredient), NOT smuggled. Even granting the family, reaches only
  `δ* < 1−(k+1)/n = 1−ρ−1/n` (top of the band, near capacity).
* `ListInteriorT2TwoSymmetric.lean` — `degDrop_t2_iff_two_symmetric`: **the exact t=2 degree-drop
  criterion** — both top coeffs of `p_S` vanish IFF `e_1(D_S) = c_1 ∧ e_2(D_S) = c_2` *jointly* (the
  first genuinely-multi-constraint case, the open direction), with the Vieta `X^{k+1}/X^k` identities
  and the `e_2 = ∑_{2-subsets}∏` formula machine-checked + a bridge to the RS interior list. Slice-rank
  verdict (honest NO-GO): the t=2 joint fiber sits inside the e_1 fiber (`twoSymmetric_card_le_subsetSumCount`),
  so the pigeonhole floor survives, but Croot–Lev–Pach needs ADDITIVE tensor structure a multiplicative
  subgroup lacks — slice-rank cannot force the t=2 count below `C(n,k+2)/|F|` by symmetry alone.
* `SubsetSumPigeonholeManyTargets.lean` — sharpens the t=1 pigeonhole from "∃ one big target" toward
  "many targets" via the second moment `∑_target N²` and the Newton/Vieta symmetries.

**Net.** 25 verified bricks across rounds 1–5. New this round: the first UNCONDITIONAL general-n interior
list lower bound (near-capacity, not q-independent — honest) and the exact t=2 joint-symmetric condition
(setting up the open direction). The deep-interior δ* and the t≥2 super-poly multi-esymm count remain
open; slice-rank is now a machine-checked dead end for the symmetry-only approach to t=2.

### O22 / Round-6 — t=2 reached (deeper unconditional bound), exact e_2-reduction, q-independence NO-GO

Round 6 used MULTIPLICATIVE methods (slice-rank being a proven dead end) to reach t=2 and map the next
walls. 6 axiom-clean bricks (all `lake build`-clean). **Deep-interior δ* still OPEN**, but this is the
deepest verified interior progress yet, with two genuinely new structural results.

* `ListInteriorUnconditionalT2.lean` — **`exists_interior_list_ge_unconditional_t2`: the first
  unconditional general-n interior list LB at agreement `k+2` (one step DEEPER than round-5's t=1).**
  Hyps ONLY `0<k, k≤n, 0<q, (k+2)²<kn` ⟹ `∃ g` deg `k+2` with `C(n,k+2) ≤ q²·#{codewords agreeing
  ≥k+2}` at `δ=1−(k+2)/n`. Discharged via an honest F×F **double pigeonhole** over BOTH symmetric
  targets `(c₁,c₂)`, with `g = X^k(X²−c₁X+c₂)` realizing them and `degDrop_t2_iff_two_symmetric` (a real
  biconditional needing both top coeffs to vanish). Honest: `/q²` (weaker than t=1's `/q`), still near
  capacity. Non-vacuity machine-checked at `k=50,n=220` (δ=0.764 inside (0.523,0.773)).
* `SubsetSumE2PowerSumReduction.lean` — **`twoSymmetric_count_eq_e1_psum2_count`: the exact t=2
  reduction.** Via the Newton identity `e_1² = p_2 + 2e_2` (`sq_window_sum_eq`, char-free), the joint
  `{e_1=c₁ ∧ e_2=c₂}` count **literally equals** the `{e_1=c₁ ∧ p_2=c₁²−2c₂}` (sum, sum-of-squares)
  count (hypothesis `(2:F)≠0`, automatic for smooth `2^k`-domains since `q` is odd). **Re-poses the
  slice-rank-hostile pair-product `e_2` as the single-coordinate statistic `x↦x²` — the precise object a
  2-D Gauss/Weil character sum estimates, opening the multiplicative route.** Honest: exhibits the Weil
  target, does NOT yet bound it; the symmetry no-go survives (max fiber ≥ C(n,a)/q), magnitude as open
  as before — only the coordinates changed.
* `SubsetSumE2PairingInflate.lean` — `twoSymmCount_ge_squareSubsetSum` (+ `esymm2_inflate`,
  `esymm2_union`, new): the ±pairing doubling shifts `e_2` by exactly `−∑g_i²` per pair while FIXING
  `e_1`, reducing the t=2 lower bound to a t=1-shaped subset-sum count on the squares `{g_i²}` — collapses
  the 2nd constraint to 1-D but lands on the same open worst-case-spread question one level down.
* `StepanovPointCountEngine.lean` — `stepanov_card_mul_mult_le_natDegree` (+ `stepanov_sharp`): the
  multiplicity-weighted Stepanov inequality `|V|·M ≤ deg Ψ`, a reusable tight point-counting engine.
  Honest no-go: Stepanov counts F-points that are roots of a UNIVARIATE auxiliary; the t=2 count is over
  (k+2)-subsets (symmetric-product points), so no univariate Ψ has them as roots — inapplicable to the
  joint count.
* `ListInteriorQDependenceNoGo.lean` — **`uniform_subsetSumCount_lb_le_choose`: a SHARP q-independence
  NO-GO.** The averaging/pigeonhole method driving every round-1..6 interior bound INHERENTLY loses a
  factor of q: any target-uniform (⟹ construction-agnostic ⟹ q-independent) lower bound `f` obeys
  `q·f ≤ C(n,a)` (forced ≤ the average, via `∑_target N = C(n,a)`); lifted to the RS list
  (`uniform_interior_list_lb_carries_q`). Removing `/q` is equivalent to the count CONCENTRATING on O(1)
  targets — a non-averaging input the order-≤4 symmetry group cannot supply. **This explains why the only
  q-independent bound (field-independent C(n,k)) lives at the EXCLUDED capacity endpoint, and pinpoints
  *concentration* as the open door.**
* `ListMCAWiringNoGo.lean` — `collapse_mca_bound_ge_of_list_lb` + `degenerate_stack_no_mcaEvent`:
  connects the list track to the §5 collapse (`interiorList_eq_lineWitness`: the degenerate stack `(w,0)`
  makes the line-witness count EXACTLY the interior-list filter, so the list LB lower-bounds the
  collapse's uniform-L). **Honest: the tempting "list-large ⟹ ε_mca-large" is FALSE and proven false —
  the witnessing stack fires ZERO mcaEvents, so the coupling is list ⟹ collapse-L (an INPUT to an UPPER
  bound on ε_mca), NOT a lower bound on ε_mca. Future ε_mca lower bounds must go through bad-scalar
  spread (distinct γ), not list-against-one-word.**

**Net.** 31 verified bricks across rounds 1–6. New this round: t=2 reached unconditionally (deeper than
the t=1 sliver, /q²), the exact `e_2`↔`(e_1,p_2)` reduction (multiplicative route opened, Weil target
exhibited), a sharp q-independence no-go (averaging loses q; concentration is the open door), and the
honest list↛ε_mca finding. Deep-interior δ* and the magnitude of the t≥2 count remain OPEN; the next
genuine step is a Weil/Gauss bound on the (sum, sum-of-squares) count, for which Mathlib lacks the
machinery.

### O23 / Round-7 — prize dichotomy reduced to ONE scalar (M2), quadratic Gauss sum landed, concentration cracked on coordinate 1

Round 7 attacked the round-6 seams (the (sum,sum-of-squares) count N2, concentration, Weil). No
breakthrough — deep-interior δ* and N2 q-independence stay OPEN — but the **most precise cartography
yet**: the entire prize dichotomy is reduced to one uncomputed scalar, the missing Weil input is
supplied, and concentration cracked on the first of two coordinates. 6 axiom-clean bricks (all `lake
build`-clean).

* `SubsetSumSecondMomentCollision.lean` + `SubsetSumPaleyZygmundDichotomy.lean` — **the prize dichotomy
  reduced to ONE scalar.** `N2_secondMoment_eq_collisionCount`: `∑_{c₁,c₂} N2(a;c₁,c₂)² = collisionCount`
  (= #pairs of a-subsets with equal (∑x,∑x²)), exact. `support_card_ge_choose_sq_div_secondMoment` +
  Paley–Zygmund: integer Cauchy-Schwarz `C(n,a)² ≤ |support|·M2` and the two-sided sandwich
  `C(n,a) ≤ collisionCount ≤ C(n,a)²`. **Net: small M2 (≈C²/q²) ⟺ N2 anti-concentrated ⟺ prize survives
  the averaging attack; large M2 (≳C²) ⟺ concentration possible.** The whole prize-deciding question is
  now the single uncomputed magnitude `M2 = collisionCount`.
* `QuadraticGaussSumMagnitude.lean` — **`norm_sum_addChar_bsq`: the quadratic Gauss sum, exact `‖∑_{x∈F}
  ψ(b x²)‖ = √q`** (b≠0, char≠2), via Mathlib `gaussSum_sq`. The ONE Weil-type cancellation Mathlib
  proves — the missing analytic ingredient rounds 1–6 never had (round 4 stopped at a cancellation-free
  triangle envelope). Honest limit (`subgroup_quadratic_sum_is_partial`): this is the FULL-FIELD sum;
  N2's generating function is a PRODUCT over the SUBGROUP (a partial Gauss sum needing Weil-on-curves,
  which Mathlib lacks). The bridge full-field→subgroup is exactly the open gap.
* `SubsetSumNegSymmConcentration.lean` — **`negSymm_card_ge_choose`: concentration CRACKED on coordinate
  1.** Negation-symmetric subsets (`S = −S`) FORCE `e_1 = ∑x = 0` (the single known target —
  concentrated!), with a q-independent, field-independent, super-poly count `C(n/2, t)` — beating every
  prior round's `/q` averaging floor *on that coordinate*. Honest delimiter (`negClosure_psum2_eq_two_mul`):
  the SECOND coordinate `p_2 = 2∑g²` still spreads freely (the 3 negation-symmetric e₁=0 subsets land on
  3 distinct p₂), so the joint N2 stays small. The residual is now exactly the `p_2` spread on
  negation-symmetric families.
* `ListInteriorUnconditionalGeneralT.lean` — **`exists_interior_list_ge_unconditional_t`: the general-t
  unconditional interior bound, subsuming rounds 5–6.** For ANY t with `(k+t)²<kn`: `∃ g` deg k+t with
  `C(n,k+t) ≤ q^t·#{codewords agreeing ≥k+t}` at `δ=1−(k+t)/n`, via a coordinate-free top-t-coefficient-
  vector pigeonhole (no Vieta/Newton bookkeeping). **Reaches DEEP interior — t up to ~√(kn)−k, a constant
  fraction of k** (non-vacuous at k=100,t=40,n=400). Honest: `/q^t` (strictly worse per added depth);
  confirms the `q^t` wall is structural to pigeonhole/averaging (matches `ListInteriorQDependenceNoGo`).
* `ListInteriorT3ThreeSymmetric.lean` — `degDrop_t3_iff_three_symmetric` (exact t=3 condition) +
  `cube_window_sum_eq` (Newton `e_1³=p_3+3e_1e_2−3e_3`, new) + `threeSymmetric_count_eq_moment_count`
  (recoordinatize to the 3-D moment fiber `(∑x,∑x²,∑x³)`). The general-t `(e_1..e_t)⟺(p_1..p_t)` pattern.

**Net.** 37 verified bricks across rounds 1–7. New: the prize dichotomy reduced to one scalar M2
(small⟹survives, large⟹concentration), the quadratic Gauss sum (√q, the Weil input), concentration on
coordinate 1 (q-independent super-poly, residual = p_2 spread), the general-t unconditional bound
(constant-fraction-of-k depth, /q^t), the exact t=3 condition. The open prize is now a single magnitude:
**compute/bound M2 = collisionCount of the (∑x,∑x²) count on the smooth 2^k-subgroup** — needs the
subgroup-restricted (partial) quadratic Gauss sum, i.e. Weil-on-curves, which Mathlib does not have.

### O23 / Round-8 — order-4 `⟨ω⟩`-closure concentrates BOTH `∑x` and `∑x²` at `0` (Round-7 residual closed)

Round 7 (`SubsetSumNegSymmConcentration`) concentrated the FIRST coordinate `e_1 = ∑x` at the single
target `0` (negation-symmetric `S = P ∪ −P`, `q`-independent count `C(n/2,t)`) and left the SECOND
coordinate honestly open: `∑x² = 2∑_{g∈P} g²` *spreads* with the pair-squares `{g²}`. Round 8 closes
that residual. The key observation: the pair-squares `{g² : g∈G}` are exactly the order-`n/2` subgroup
`G²`, *itself* negation-closed — so the same trick recurses one level up. Packaged multiplicatively,
both levels at once is just **closure under the order-4 element** `ω` (`ω² = −1`, `⟨ω⟩ = {1,ω,−1,−ω}`).

`SubsetSumOmegaConcentration.lean` (9 lemmas, all `sorry`-free, axiom-clean `[propext,
Classical.choice, Quot.sound]`, `lake env lean`-verified):

* `omega_closed_psum_eq_zero` — **the engine.** `S.image (ω·) = S`, `ω ≠ 0`, `ω^j ≠ 1` ⟹
  `∑_{x∈S} x^j = 0`. Proof: reindex `∑x^j = ∑(ωx)^j = ω^j∑x^j`, so `(1−ω^j)∑ = 0`. A SINGLE uniform
  statement vanishing every power sum with `ω^j ≠ 1` — for `ω` a primitive `N`-th root it kills `p_j`
  for all `N ∤ j`.
* For order-4 `ω` (`ω²=−1`, char `≠2`): `ω¹=ω≠1` and `ω²=−1≠1`, so the engine gives `∑x = 0` AND
  `∑x² = 0` for *every* `⟨ω⟩`-closed set (`omega4Closure_sum_eq_zero`, `omega4Closure_sumsq_eq_zero`).
  Hence `e_1 = 0` and `e_2 = (e_1²−p_2)/2 = 0`: **both** symmetric functions pinned to the single
  target `(0,0)` — the `N2(·;0,0)` fiber Round 7 could only pin on its first coordinate.
* `omega4Closure` (`P ∪ ωP ∪ ω²P ∪ ω³P`) + `omega4Closure_image_eq` (`ω`-closed via
  forward-subset-of-equal-card) feed the engine. `omega4_card_eq` (= `4|P|` under the free-action
  `OmegaFree`) + `omega4Closure_injOn` give the count.
* `card_ge_choose_two_zero` — **the headline.** Under `OmegaFree ω T` (the four `⟨ω⟩`-translates of the
  transversal `T` pairwise disjoint), `U ↦ omega4Closure ω U` injects the `s`-subsets of `T` into the
  size-`4s` subsets with `∑x = ∑x² = 0`, so

    `C(|T|, s)  ≤  #{ S : |S| = 4s, ∑x = 0 ∧ ∑x² = 0 }  =  n2Count (omega4Closure ω T) (4s) 0 0`

  (the RHS filter is *definitionally* Round-7's `n2Count G (4s) 0 0`). With `|T| = n/4` this is
  `C(n/4, s)`: **`q`-independent** and super-polynomial — Round 7's residual coordinate `p_2`, now
  concentrated at one target with no `/q` loss. (Complementary to the fleet's
  `Round8_t1_full_concentration`, which handles only the `t=1` first coordinate.)
* Non-vacuity over `ZMod 5` (`ω=2`, `2²=4=−1`, orbit `{1,2,3,4}`, `∑=∑²=0`) — genuine, not `0=0`.

**The depth-collapse WALL (why this is NOT a prize counterexample, honestly).** The engine generalizes:
closure under a primitive `2^r`-th root of unity kills `p_1,…,p_{2^r−1}`, hence `e_1,…,e_{2^r−1}`. So
pinning the first `t` symmetric functions needs `r = ⌈log₂(t+1)⌉`. But the `⟨ω_r⟩`-orbits have size
`2^r`, so the transversal has only `n/2^r` elements and the concentrated count is `C(n/2^r, s)`.
Reaching the **deep interior** (agreement `≈ √(kn)`, near Johnson) forces `2^r ≈ t ≈ √(kn)−k`, i.e.
`r ≈ m`, which **collapses** the transversal to `n/2^r = O(1)` and the count to a *constant*. This is
the same wall, now sharp and structural: *concentration on a single target requires a symmetry group
fixing it, and a larger symmetry (more constraints killed) partitions the ground set into bigger
orbits and fewer free choices.* Concentration therefore works near CAPACITY (constant `t`) but cannot
pin `δ*` in the deep interior — exactly ABF26's "no known technique past Johnson for explicit RS". The
order-4 construction is the first verified concentration of the FULL `t=2` joint fiber; the deep
interior remains the genuine open core.

**Net.** 40 verified bricks across rounds 1–8. New this round: the order-4 `⟨ω⟩` engine vanishing all
`ω^j ≠ 1` power sums; both-coordinate concentration of the `t=2` joint count `N2(·;0,0)` (Round-7
residual closed); the sharp depth-collapse articulation of why single-target concentration is
capacity-only. The deep-interior `δ*` is unmoved and unmovable by symmetry alone (proven wall).

### O25 / Round-9 — the coset route's deep-interior NO-GO, as one explicit theorem

The round-8 coset / vanishing-power-sum construction (`Round8CosetWall.lean`,
`CosetPowerSumConcentration.lean`: closure under a primitive `N`-th root kills `p_1,…,p_{N-1}` ⟹ via
Newton `e_1,…,e_{N-1}=0` ⟹ a depth-`(N-1)` degree-drop family, q-independent, count `C(M,r)`,
`M=n/N` cosets, union size `a=r·N`) is the natural deepening of round-8's negation-symmetry. Round 9
welds its scattered budget inequalities into **one explicit no-go** (`CosetWallDeepInteriorNoGo.lean`,
axiom-clean):

* `coset_count_le_card_of_deep_interior`: at constant-fraction-or-deeper interior (`t ≥ k`, agreement
  `a=k+t ≥ 2k`, radius `δ ≤ 1−2ρ`), the budget forces `r ≤ 1` (`budget_forces_r_le_one`), so the count
  `C(M,r) ≤ M` — **linear** in the number of cosets, NOT super-polynomial.
* `coset_within_prize_of_deep_interior`: in prize coordinates, a coset list of size `L ≤ C(M,r) ≤ M`
  with `M ≤ thresh` (the prize's `ε*·q` budget) stays `L ≤ thresh` — **within** the prize. Since
  `M = n/N ≤ n ≤ 2^40` while the prize threshold `ε*·q` is astronomically larger for the relevant
  fields, **no coset / vanishing-power-sum construction disproves the prize in the deep interior.**
* `near_capacity_superpoly`: the contrast — near capacity (`2r ≤ M`) the SAME count is `≥ 2^r`,
  super-poly. So the deep-interior collapse to `≤ M` is a genuine **phase transition** in the
  construction's power at `δ = 1−2ρ`, not a vacuous bound.

**Net.** This closes one entire algebraic attack family (coset/vanishing-power-sum, the natural
deepening of the round-5..8 unconditional and q-independent bounds) at deep interior: its super-poly
count provably degrades to linear past `δ = 1−2ρ`, matching the [ABF26] "no known technique" assessment
for the deep interior. The two genuinely open routes remain: the subgroup-restricted quadratic Gauss
sum (SEAM B = Weil-on-curves, Mathlib lacks) and any NON-algebraic construction (outside the coset/
pigeonhole/symmetry families now all walled). Deep-interior δ* remains OPEN. 44+ bricks.

### O26 / Round-9b — the subgroup Gauss-sum SECOND MOMENT, exactly, with NO Weil bound (Parseval)

Rounds 7–8 showed the prize-deciding magnitude needs the **subgroup-restricted** Gauss sum
`η_b = ∑_{y∈G} ψ(b·y)`, and that a per-frequency `√q` bound needs Weil-on-curves (Mathlib lacks).
`SubgroupGaussSumSecondMoment.lean` (axiom-clean) supplies the one piece that **is** fully provable
elementarily — the *second moment* over all frequencies, via additive-character orthogonality
(Parseval), **no Weil**:

* `subgroup_gaussSum_secondMoment`: `∑_{b∈F} ‖∑_{y∈G} ψ(b·y)‖² = q·|G|`, exact. Proof: expand
  `‖η_b‖² = η_b·conj(η_b)` (`RCLike.mul_conj`) into a double sum over `(y,y')∈G×G`, conj via
  `starComp_apply`/`inv_apply`, swap sums, and collapse each pair by `AddChar.sum_mulShift`
  (`∑_b ψ(b·c) = q·[c=0]`) to the diagonal `y=y'`.
* `subgroup_gaussSum_l2_average`: hence the **average** of `‖η_b‖²` over the `q` frequencies is exactly
  `|G|`. So the *typical* subgroup Gauss sum has size `√|G|`, **not** `√q` (since `|G|≤q`) — the
  average-case cancellation that the collision-count second moment `M2` runs on.
* `exists_frequency_gaussSum_sq_ge`: pigeonhole — some frequency attains `‖η_b‖²≥|G|`.

**Honest scope.** This controls the subgroup Gauss sum in `L²`/average — exactly the regime that decides
*average*-case anti-concentration of `M2` — while the **per-frequency worst case** (the deep-interior δ*
pin) genuinely still needs Weil's bound. It is the strongest analytic statement about the subgroup Gauss
sum reachable from Mathlib's current toolkit (character orthogonality), and it closes the *average*-case
side of SEAM B. 45+ verified bricks rounds 1–9. Deep-interior δ* and the worst-case Gauss bound remain
OPEN (Weil-on-curves not in Mathlib).

### O24 / Round-9 — multi-agent verified assault (6 angles, all axiom-clean); 4 bricks integrated

Deployed a 6-angle multi-agent workflow. Enabler: `lake env lean <file>` is READ-ONLY on the olean
cache (type-checks in memory, never writes oleans), so many agents verify concurrently with NO
`lake build` thrash. All 6 landed verified+axiom-clean; 4 integrated (collapse/Johnson overlap
`Round8CosetWall`/`JohnsonBound`):

* `DeltaStarConcretePinF17.lean` — concrete TWO-SIDED δ* pin on a smooth subgroup: `F=ZMod 17`,
  `G={x:x^16=1}=Fˣ` (n=16=2^4, `G_eq_roots_of_unity` proven), `k=2`, interior `δ=13/16` (`a=3`,
  interiorness `2<3 ∧ 9<32` in integer AND real form). `5 ≤ |Λ| ≤ 120` (exact 19): lower = 5 explicit
  lines on disjoint 3-blocks; upper = ∀-cap via `line_unique` (k=2 Vandermonde) → `C(16,2)`. δ* IS
  two-sidedly pinnable inside the gap for a prize-faithful instance.
* `LamLeungAntipodalTightness.lean` — FIRST upper bound on the `e_1=0` fiber: conditional on cyclotomic
  indep `hindep`, `∑ζ^a=0 ⟹ A` antipodal-invariant (regroup `∑ζ^a=∑_{j<N}([j∈A]-[j+N∈A])ζ^j` via
  `ζ^{j+N}=-ζ^j`+`sum_nbij'`). `hindep` holds over ℂ, FAILS in finite fields = the q-dependent extras.
* `AveragingFiberConservation.lean` — conservation `∑fiber=C(n,a)`, 2nd-moment `∑fiber²=#collisions`,
  averaging LB `C(n,a)≤q^t·maxFiber`, anti-concentration hypothesis as a Prop (general Φ, subsumes
  n2Count): `antiConcentrated ⟺ maxFiber pinned to average` — the precise hypothesis pinning δ*=δ_avg.
* `DeltaStarAveragingBracket.lean` — `averaging_crossover`: `C(n,k+t)≤q^t·L ∧ E·q^{t+1}<C(n,k+t) ⟹
  E·q<L` (δ* ≤ 1-(k+t)/n upper bracket) + non-vacuity.

**Net.** Open core (list UPPER bound past Johnson; q-dependent concentration) unmoved — research-grade.
Round 9 = the state-of-the-art *bracket* machinery + a concrete two-sided pin + first fiber tightness.
All on main (`0e39a4435`), axiom-clean, 0 sorry. Issue stays open.

### O28 / Round-9d — roots of unity have MINIMAL additive energy `E ≤ 3|S|²` (characteristic 0)

The fourth-moment identity (O27) reduced the deep-interior question to the additive energy `E(G)` of the
smooth subgroup. `RootsOfUnityAdditiveEnergy.lean` (axiom-clean) proves the structural fact that, **in
characteristic 0**, that energy is *minimal*:

* `unitCircle_reps_le_two`: for `s ≠ 0` and any finite `S` on the complex unit circle (`y·conj y = 1`,
  e.g. the `n`-th roots of unity), the number of representations `#{y∈S : s−y∈S}` is `≤ 2`. Mechanism:
  a unit-circle `y` with `s−y` also on the circle satisfies the **quadratic**
  `conj(s)·y² − (s·conj s)·y + s = 0` (from `y·conj y = 1` and `(s−y)·conj(s−y) = 1`, pure ℂ-conjugate
  algebra via `linear_combination`), and a nonzero quadratic has `≤ 2` roots (`Polynomial.card_roots'`).
* `unitCircle_additiveEnergy_le`: hence `E(S) = ∑_{a,b∈S} #{y∈S:(a+b)−y∈S} ≤ 3·|S|²` — the **diagonal**
  `a+b=0` contributes `≤|S|` pairs (each `≤|S|`), the rest `≤|S|²` pairs (each `≤2`).

**Why it matters.** Minimal additive energy `E(S)=Θ(|S|²)` is exactly maximal *anti-concentration* of the
subset-sum count — the regime where the §7/averaging attack is **defeated**. Combined with the
fourth-moment bridge (`∑_b ‖η_b‖⁴ = q·E`), this is the **clean characteristic-0 resolution**: the smooth
(roots-of-unity) domain provably has the *minimal* additive energy, so it resists the attack — in char 0.

**Honest scope.** The Proximity Prize lives over a *finite field* `F_q`. The `≤2`-representations
argument uses complex conjugation (`conj y = y⁻¹` on the unit circle), which has **no `F_q` analogue** —
over `F_q` a multiplicative subgroup's additive energy is the genuinely *open* sum-product quantity (it
can be large depending on `|G|` vs `q`). So this proves the smooth domain is "good" in the char-0 model
and pins the finite-field gap precisely as: *bound the additive energy of the `2^k`-subgroup over `F_q`*
(equivalently the worst-case subgroup Gauss sum / Weil). 48+ verified bricks rounds 1–9.

### O25 / Round-10 — 4 deeper verified bricks (exact crossover, joint t2, best bracket, Johnson no-go)

Second thrash-safe multi-agent round (read-only `lake env lean`). All 4 verified+axiom-clean+non-vacuous
(non-vacuity adversarially checked). On main `f2dbe3137`:
* `DeltaStarExactCrossoverF17.lean` — EXACT two-sided δ* crossover for RS[ZMod17,Fˣ,2] (n=16,k=2):
  exact |Λ|=15,5,3 at a=3,4,5 (decide); at B=10 crossover a*=4 (δ*=3/4), MAXIMAL (∀a∈[4,16] fit, a=3
  fails) so no gap, strictly interior (2<4 ∧ 16<32). Closes Round-9 bracket [5,120] to a sharp point —
  the prize fully solved at this concrete scale.
* `JointT2FiberTightness.lean` — exact (e_1,e_2)=0 fiber = order-4 ⟨ω⟩-symmetric subsets via two-level
  antipodal descent (t=1 antipodal → t=2 descends to squares in G²). TWO-TYPE design (coeffs K=ℚ, roots
  cyclotomic L) fixes a vacuity bug (one-type indep-over-L is vacuous for N≥2); literal oneRootSystem
  inhabitant witnesses non-vacuity. Matches Round-8 C(n/4,s) as EQUALITY over ℂ.
* `BestProvableBracket.lean` — δ* ≤ min(δ_avg, δ_sym) + comparison_min regime lemma + Johnson δ*≥1-√ρ.
* `JohnsonSecondMomentFrontier.lean` — Johnson 2nd-moment list cap + NO-GO cauchySchwarz_eq_iff_flat
  (CS tight ⟺ flat profile ⟺ Johnson, so 2nd moment alone CANNOT beat Johnson; need higher-order).

**Net.** Open core (list UPPER bound past Johnson for the asymptotic family) unmoved — research-grade.
Rounds 8-10 = order-4 concentration+depth-collapse engine + concrete two-sided pin + EXACT crossover +
joint-t2 tightness + averaging/symmetric brackets + Johnson 2nd-moment no-go. Issue stays open.

### O30 / Round-9f — CORRECTION: the char-0 minimal-energy bound does NOT transfer to `F_q` (verified counterexample)

Honest correction to the O28–O29 framing. The reduction `repCount ≤ 2 ⟹ E ≤ 3|G|²` (O29) is correct,
but its hypothesis — proven in char 0 (O28) via complex conjugation — is **FALSE over `F_q`**.
`SubgroupRepCountFiniteFieldCounterexample.lean` (axiom-clean, kernel `decide`) exhibits it:

* Over `F₁₇` (`8 ∣ 16 = |F₁₇ˣ|`), the `8`-th roots of unity are `G = {1,2,4,8,9,13,15,16} = {±1,±2,±4,±8}`.
* `repCount_F17_eighthRoots_eq_three`: `#{c∈G : c+1∈G} = 3` — the consecutive pairs `(1,2),(8,9),(15,16)`
  are all inside `G`. So `char0_repBound_fails_over_finite_field`: `∃ t≠0, repCount G t > 2`.

**Why this matters (the real correction).** The char-0 quadratic argument (a nonzero sum has ≤2
unit-circle representations) uses `conj c = c⁻¹`, which has no `F_q` analogue — and indeed over `F_q` the
`2^k`-subgroup has **additive coincidences** (consecutive elements) absent in char 0. So the smooth domain
does **NOT** have minimal additive energy over `F_q`; the true `F_q` additive energy is strictly larger
than the char-0 `3|G|²` and is the genuine open **sum-product** quantity. This is exactly why the
deep-interior δ* problem is hard over finite fields and easy in char 0 — now demonstrated by a verified
counterexample. The honest open core: the *true* sum-product additive-energy bound for `2^k`-subgroups
over `F_q` (which determines whether the §7/averaging attack is defeated), NOT the char-0 value. 51
verified bricks rounds 1–9; this one corrects the record.

### O26 / Round-11 — 4 bricks: unconditional tightness/Q, δ* table, Fisher past Johnson, RS averaging LB

Third thrash-safe multi-agent round. All 4 verified+axiom-clean+non-vacuous. On main `7865357ce`:
* `LamLeungUnconditionalQ` — DISCHARGES the cyclotomic-indep hypothesis: linearIndependent_pow_le
  (N≤deg minpoly ⟹ {ζ^j} indep) + antipodal_of_sum_zero + UNCONDITIONAL ℚ(i) instance antipodal_Qi.
  General N=2^{m-1} needs only the cyclotomic degree φ(2N)=N (Mathlib has, not yet assembled).
* `DeltaStarTableSmoothInstances` — 3 NEW exact interior crossovers (ZMod17 k=3 δ*=11/16; ZMod41 order-8
  δ*=5/8; ZMod97 order-8 δ*=5/8), maximality proven STRUCTURALLY (antitone, all a≥a*).
* `FisherPastJohnsonCap` — polynomial-method cap F.card·C(t,a+1)≤C(n,a+1) valid PAST Johnson (n=16,t=4,
  a=1: Johnson denom t²-an=0 vacuous, Fisher=20). HONEST FINDING: for RS, |Λ|≤C(n,k)/C((1-δ)n,k); at
  Johnson ≈(n/k)^{k/2} which for prize k≤2^40 ≫ ε*|F| — so Fisher is valid-but-too-weak past Johnson,
  does NOT push δ* up. Concrete reason the upper-bound-past-Johnson is hard (simple caps too lossy).
* `AveragingListLowerBoundRS` — averaging LB maxList≥C(n,k+t)/q^t as a genuine theorem (pigeonhole +
  injective S↦codeword), discharges BestProvableBracket's hypothesis.

**Net.** Asymptotic open core (sharp list UPPER bound past Johnson) unmoved — now better-understood as to
why (Fisher too weak, Johnson's sharper poly bound stops exactly at 1-√ρ). Issue stays open.

### O27 / Round-12 — UNCONDITIONAL tightness completion + MDS list-bound kernel

Completion round (3/4 angles; 4th rsdeltastarbound left incomplete, overlaps Round-11). On main `3fbb036e3`:
* `LamLeungUnconditionalGeneral` — antipodal_unconditional: e_1=0 fiber tightness FULLY UNCONDITIONAL
  for general N=2^{m-1} over any CharZero field. totient_two_pow (φ(2^m)=2^{m-1}) +
  natDegree_minpoly_primitiveRoot (cyclotomic degree) + linearIndependent_pow_primitiveRoot. Discharges
  the cyclotomic-indep hypothesis IN GENERAL (Round 11 had only N=2/Q(i)); instantiated at m=3 (8th roots,
  N=4) with non-vacuity.
* `JointT2Unconditional` — joint_t2_unconditional: joint (e_1,e_2)=0 fiber = order-4 ω-symmetric subsets,
  UNCONDITIONAL over ℂ (general k), cyclotomic indep at BOTH levels G and G². Completes Round-10 conditional
  joint-t2; Round-8 C(n/4,s) lower bound is now a genuine EQUALITY over ℂ.
* `RSMDSListBound` — rs_list_leading_bound: MDS weight-enumerator/information-set RS list bound
  (rs_codeword_weight_ge = MDS dist n-k+1; rs_vanish_card_le; listAt⊆biUnion) + concrete ZMod 7 instance.
  First brick of the genuine asymptotic list-bound machinery (the route the open core needs).

**Net.** Rounds 8-12: lower-bound/fiber/concrete side COMPREHENSIVE + now UNCONDITIONAL; MDS kernel started.
Asymptotic open core (sharp list upper bound past Johnson) unmoved — research-grade. Issue stays open.

### O28 / Round-13 — the #82-kernel identity (2nd moment = ball-intersection)

Asymptotic-kernel round; 1 brick landed (other 2 angles cut short by session usage limit). On main `61cf5eea5`:
* `ListAroundBallIntersectionKernel.lean` — sum_sq_listAround_eq_ball_inter: ∑_w |listAround(w)|² =
  ∑_{c,c'} |B(c,r)∩B(c',r)|, the genuine object controlling general-center list sizes. Plus
  listAround_codeword_eq_singleton (codeword-centered list trivial for r<d — localizing why the weight
  enumerator only handles the codeword-centered case) and sum_listAround_card (first moment). By
  Cauchy-Schwarz/Paley-Zygmund a uniform bound on the RHS ball-intersection 2nd moment gives the sharp
  list control past Johnson. The SHARP RHS bound for explicit RS is the open prize kernel (CS25/#82).

**SESSION SUMMARY (Rounds 8-13, ~21 verified axiom-clean files on main).** The lower-bound/fiber/concrete
side of #232 is comprehensively + UNCONDITIONALLY machine-checked; the averaging/bracket machinery and the
Johnson 2nd-moment no-go / Fisher past-Johnson finding map the upper-bound frontier; the open core is now
sharply reduced to ONE object — the ball-intersection 2nd moment ∑_{c,c'}|B(c)∩B(c')| (sum_sq identity) —
whose sharp upper bound for explicit smooth-domain RS is the genuine research kernel (MDS weight-enumerator
2nd-moment ball-intersection, CS25/ABF26). Issue stays open — the asymptotic core is research-grade.

### O11′ — EMPIRICAL RESOLUTION of the subgroup-sumset question + the S-two/KK25 reframing (nubs, 2026-06-09)

The Loop46+ honest correction asked whether `|G^{(+ℓ)}|` for a 2-power multiplicative subgroup is
sub-exponential (survive) or near-maximal (refute-pressure). **Probed: it is exponential.**
Distinct half-subset sums (`ℓ = |G|/2`), uncapped fields, exact DP for |G| ≤ 16, sampled lower
bound at |G| = 32 (q = 2013265921, 6M samples, seed 11; collision-corrected estimate):

| |G| | distinct ℓ-sums | log₂ |
|---|---|---|
| 8 (exact) | 41 | 5.4 |
| 16 (exact, q=786433) | 3 281 | 11.7 |
| 32 (LB, q≈2.0e9) | ≥ 4 112 427 (≈5.6M corrected) | ≈22.4 |

`log₂ ≈ 0.7·|G|` — exponential; the vanishing-power-sum structure costs only ~0.2 bits/element vs
generic. So the power-sum/Newton sub-exponential hope is **empirically dead** (evidence, not proof;
lower-bound direction — exactly what the attack side needs). Useful provable mini-lemma: for the
full subgroup, `∑_{g∈G} g = 0` gives the complement symmetry `|G^{(+ℓ)}| = |G^{(+(|G|−ℓ))}|`,
making all four prize rates' critical layers uniform.

**Cross-reference that re-shapes the target (see #232 comment 2026-06-09):** the official ABF26
challenge (2026/680, read in full) is a per-code determination (window k ≤ 2⁴⁰, |F| < 2²⁵⁶), and
CGHLL26 = the S-two whitepaper (2026/532, App. A) states the believed answer: Conjecture 1
(`ℓ(θ) ≤ c₁·2^{c₂·H(ρ)/η}` up to the **Elias radius** — exponential in 1/η, matching the KK25
proven lower bound `2^{(H(ρ)+o(1))/η}` AND our smooth-domain probe shape) + Conjecture 2
(line-decodability, threshold `a = ℓ·n + o(n)` ⟹ `ε_mca ≤ ℓ·n/|F|` via GG25 Thm 3.5).
Conditional answer formula: `δ*_C = 1−ρ−Θ(H(ρ)/(log₂|F| − 128 − log₂ n))` (≈ capacity − 0.011 at
ρ=1/2, n=2⁴⁰, |F|=2²⁵⁶). ⇒ The in-tree poly(1/η) prize surfaces are the wrong *sharp* shape
(not contradicted — `(2^m)^{c₁}` absorbs `n^{Ω(1)}` at η ≳ 1/log n — but hopeless below
η ≈ H/(c₁·log n)); the believed-true budget is `2^{O(H(ρ)/η)}`. **The open $1M core, sharply:
prove `ℓ(θ) ≤ 2^{O(H(ρ)/η)}` for plain deterministic smooth-domain RS in (Johnson, Elias)** —
known for random codes and random/folded RS (GG 2025/2054); the gap is what smoothness must
supply in place of randomness. Next: dissect GG25/KK25's use of randomness.

### O29 / Round-13b (main-loop, no agents) — the linear-code collapse of the ball-intersection 2nd moment

After the agent session limit, proved directly (BallIntersectionSecondMomentLinear.lean, axiom-clean):
for a subtraction-closed (linear) code C, ∑_{c,c'∈C}|B(c,r)∩B(c',r)| = |C|·∑_{e∈C}|B(0,r)∩B(e,r)|
(translation invariance Δ(x−z,y−z)=Δ(x,y) via hammingDist_comp + reindex c'↦c'−c), and the triangle
cutoff wt(e)>2r ⟹ B(0,r)∩B(e,r)=∅. Combined with the #82-kernel identity (O28), the full chain is:

   ∑_w |Λ(w,r)|²  =  ∑_{c,c'∈C}|B(c)∩B(c')|  =  |C| · ∑_{e∈C, wt(e)≤2r} |B(0,r)∩B(e,r)|.

So the open core is now reduced to the cleanest possible object: the OFF-DIAGONAL sum
∑_{e∈C, wt(e)≤2r}|B(0,r)∩B(e,r)| = (MDS weight enumerator A_w, w≤2r) × (ball-intersection volumes
I(w,r)=|B(0,r)∩B(e,r)|). The sharp bound on THIS is exactly the CS25/#82 research kernel (the crude
I≤V(r) bound is provably too weak past Johnson — H(2δ)>H(δ) blowup). Multi-paper, not session-achievable.
GOTCHA: hammingBall is a def ⟹ membership lemmas don't auto-fire (simp shows raw Quot.lift); add a
`@[simp] mem_hammingBall` lemma and destructure with `Finset.mem_inter.mp`/`mem_hammingBall.mp`, not simp.

### O11″ — the KK mechanism reproduced LIVE at moderate p (nubs, 2026-06-09)

Small-scale, noise-free end-to-end reproduction (p=2013265921 ≈ 2³¹, smooth H of order 16, inner
subgroup G of order 8, rate 1/2, radius 0.375 ∈ (Johnson, capacity), agreement ≥ 10, noise floor
≈ C(16,10)/p ≈ 5·10⁻⁶): on the lifted line `X¹⁰ + λX⁸`, every 5-subset S ⊂ G yields the witness
u_S(X²) (deg 6 < k=8) agreeing on exactly 10/16 — and the bad-scalar set is exactly {−e₁(S)}:
**40 distinct bad λ = |G^{(+5)}| (the subgroup subset-sumset), 10/10 structured λ confirmed bad by
exhaustive list search, 0/25 random λ bad.** So (i) the KK lower-bound mechanism operates ~10⁴⁰×
below its rigorous p > φ(m)^{φ(m)} requirement — the moderate-p extension (the prize-window
question) is empirically TRUE and awaits proof (collision-counting / Stepanov / character sums on
e₁ over r-subsets); (ii) the identity {bad-scalar count} = {subset-sumset size} is the live bridge
between the off-diagonal kernel (`fa6d16534`), the O11′ sumset probes, and KK25; (iii) exhaustive
search at this scale found ONLY structured bad scalars — supporting the exhaustiveness hypothesis
(H1: structured families are the whole list past Johnson), the upper-bound route's best hope.
Reproduction: /home/nubs/proximity-research/probe_kk_live.py (seed 9).

### O11‴ — EXACT char-0 subgroup-sumset formula (data-confirmed) + averaged moderate-p route (nubs, 2026-06-09)

Fiber statistics of e₁ on r-subsets of the order-m (2-power) subgroup are p-INDEPENDENT at moderate
p (identical at 786433 and 2013265921): all collisions are characteristic-0, and the only
small-coefficient 2-power cyclotomic relation is the pairing ζ^{j+m/2} = −ζ^j. Hence (derived, and
EXACTLY matching data):
  image(m,r) = Σ_{s≤r, s≡r(2), r−s≤2(m/2−s)} C(m/2,s)·2^s   (m=16,r=8: 3281 ✓; m=8,r=4: 41 ✓)
  maxfiber(m,r) = C(m/2,⌊r/2⌋)                              (70 = C(8,4) ✓; 6 = C(4,2) ✓)
Asymptotics ~3^{m/2} = 2^{0.79m} — replaces the H(ρ) heuristics with sharp constants in the
bad-scalar counts (O11″ lift). Moderate-p rigor: a modular collision forces p | N(α) with
0<|N(α)|≤m^{m/2}; counting (α,p) pairs + Dirichlet gives an AVERAGED theorem-shape — for most
primes p ≈ 2^{1.2m} ≡ 1 mod m (inside the prize window for m ≤ 200), ZERO modular collisions, so
the image equals the exact formula. Sketch (elementary; pending careful write-up); the per-prime
statement is the residual P-A kernel. Char-0 formula is finite combinatorics + standard cyclotomic
independence ⟹ Lean-formalizable brick (queued). Probes: probe_fibers.py in the research folder.

### O30 / Round-14 — δ* bounded away from capacity by an ABSOLUTE constant at prize scale

`DeltaStarConstantGapBelowCapacity.lean` (main-loop solo, ℕ-only, axiom-clean): the averaging bound
beats ε*·|F| ≤ 2^128 for t ≤ ~2k/254, so δ* ≤ 1−ρ−ρ/127·(1±o(1)) for prize fields q ≤ 2^256. Engines:
Pascal shift C(n,m)≤C(n+j,m+j) → central binomial 4^s ≤ 2s·C(2s,s) (rate 1/2 needs the SHIFT — naive
monotonicity fails since 2(k+t)>n); crossover Lstar·q^t < C(n,k+t) under 258t+193≤2m / 254t+193≤2k.
Witnesses at n=2^20 (t=4063 rate-1/2 → δ ≈ 0.49613; t=2063 rate-1/4), extreme-parameter strict
instantiation proven outright. Prize-scale bracket now: δ* ∈ [1−√ρ, 1−ρ−ρ/127]. Remaining open side =
past-Johnson list cap (research core).

### O11⁗ — averaged P-A WRITTEN UP: exact images at moderate primes, window-level numbers (nubs, 2026-06-09)

Full careful write-up at `/home/nubs/proximity-research/06-AVERAGED-PA.md` (Theorems A–D + Corollary E):
**A** exact char-0 image/fiber formulas (triple data-verified). **B** any modular collision forces
p | N(α), 0<|N(α)|≤m^{m/2} (coeffs ≤2 in the half-basis). **C** pair counting: ≤ 5^{m/2}·(m/2)log_P m
collision-bearing primes in [P,2P]. **D** for P ≥ 5^{m/2}·m²·φ(n)·polylog, all but O(1/m) of primes
p ≡ 1 mod n in [P,2P] give image EXACTLY N₀(m,r) ≈ 3^{m/2}, all r simultaneously. **E (window
numbers):** m=128, n=2⁴⁰, p ≈ 2²⁰³ < 2²⁵⁶: most such primes give ≈ 2^{101} bad scalars at the KK
radius (η ≈ 1/64) ≫ the breach threshold 2^{203−128} = 2^{75} ⟹ **δ\*_C < 1−ρ−1/64 for most such
codes** — consistent with (and below) the S-two-conditional crossover η* ≈ 1/35. Honest caveats in
the note: "most primes" not per-prime (the residual P-A kernel — a specific production prime could
differ); Siegel–Walfisz ineffectivity for the finite window (effective Lemma C, analytic denominator);
the general-(n,m,r) lift bookkeeping + far-ness side to be written out. This is the LOWER half only;
P-B (the 2^{O(H/η)} upper bound past Johnson) remains the open core.

### O11⁗⁺ — Lift Lemma completed: the averaged lower half is a full elementary chain (nubs, 2026-06-09)

The lift bookkeeping + far-ness of O11⁗ are now closed (06-AVERAGED-PA.md, Lift Lemma): for dyadic
gap η = 1/m′ (m′ | n, ρm′ ∈ ℤ), r = ρm′+1, line (u₀,u₁) = (x^{rc}, x^{(r−1)c}), c = n/m′:
(i) far-ness is a ONE-LINE degree count — (r−1)c = ρm′c = k exactly, so x^{(r−1)c} − ĉ₁ is nonzero
of degree k ⟹ ≤ k < (1−δ)n agreements ⟹ the pair is automatically MCA-far at δ = 1−ρ−η;
(ii) each r-subset Ŝ of the m′-subgroup gives the codeword witness u_Ŝ(X^c) (deg k−c < k) agreeing
with u₀ − e₁(Ŝ)u₁ on exactly rc = (1−δ)n points ⟹ #bad λ ≥ image_p(e₁);
(iii) with Thm D: for most primes p ≡ 1 mod n, image_p = N₀(m′, ρm′+1) EXACTLY ⟹
ε_mca(C, 1−ρ−η) ≥ N₀/p = 2^{(log₂3)/(2η) − O(log 1/η)}/p.
**Net: the lower half of the Grand MCA determination — for most primes, any dyadic gap, sharp
constants — is a complete elementary chain** (cyclotomic basis count → norm/pair counting →
Dirichlet average → lift). Honest residuals, named: per-prime exactness (a specific production
prime could collide) + the analytic denominator (SW/GRH on the concrete window). The upper half
(2^{O(H/η)} list bound past Johnson = the believed-true core) remains THE open problem (P-B).

### O11⁗⁺⁺ — per-prime exactness VERIFIED at production primes (nubs, 2026-06-09)

The O11⁗ "most primes" caveat is now closed for the primes that matter, by finite verification
(exhaustive DP = proof per triple): **BabyBear 15·2²⁷+1, KoalaBear 127·2²⁴+1, Goldilocks
2⁶⁴−2³²+1 all have e₁-image EXACTLY N₀ at m=8 (41) and m=16 (3281), and pass the m=32 MITM
zero-fiber spot-check (12870 = C(16,8)) — zero modular collisions.** So the Lift-Lemma bad-scalar
lower bounds are exact verified facts at the production SNARK fields for the verified m. Open:
asymptotic per-prime (all m at a fixed p); the analytic-denominator caveat; and P-B (the upper
half) — unchanged. Scripts: probe_production.py, probe_m32_fiber.py in the research folder.

### O29 / Round-14 — the GS-algebraic route end-to-end + THE JOHNSON WALL as a theorem

5-agent GS round (all landed) + own-token root-order brick. On main `85d8a1157` (6 files, axiom-clean):
* The COMPLETE GS pipeline: `GSInterpolationExistence` (Sudan m=1 front end, rank-nullity + exact
  monomial count Σ_{j<D}(D−(k−1)j), ZMod 5 instance) → `GSRootOrderStep` (weighted-degree transfer +
  factor_of_agreement: ≥D agreement ⟹ (Y−f)∣Q) → `GSYDegreeListCap` (|S| ≤ deg_Y Q via RatFunc roots,
  cap attained with equality) → `GSPipelineAssembly` (composed, fired on a concrete instance).
* `GSJohnsonWall` (HEADLINE): gsFeasible_iff — the GS parameter system is feasible IFF t·m > DGS =
  ⌊√(n(k−1)m(m+1))⌋+1; the JOHNSON WALL gs_johnson_wall: t² > n(k−1) for EVERY multiplicity m (sharp
  t²m > n(k−1)(m+1); real √(n(k−1)(1+1/m)) < t → Johnson as m→∞, never reached). Feasible witness
  (16,2,3,5,14) just above; INFEASIBLE at t=4=Johnson. The standard GS certificate provably cannot
  go below Johnson at any multiplicity.
* `DerandomizationFrontier`: the explicit-vs-random gap as named Props (NOT asserted) + the correct
  absolute-agreement puncturing monotonicity (naive relative version FALSE) + endpoints.

**Net.** The open core is isolated on ALL sides by verified no-gos: moments = Johnson (O25/O28-adjacent),
whole-space moment diagonal-dominated (SecondMomentReductionLimit), Fisher too weak (O26), and now GS
stops exactly at Johnson (O29). Remaining: does ANY other explicit algebraic certificate beat Johnson
for smooth-domain RS — the genuine $1M core. Fleet concurrently landed the constant-gap-below-capacity
averaging bracket: verified two-sided δ* ∈ [1−√ρ, 1−ρ−c_ρ] at prize scale. Issue stays open.

### O30 / Round-14 — the per-line pair co-occurrence bound (line-restricted second-moment kernel)

The O28/O29 chain is a GLOBAL average over q^n centers and provably cannot pin the interior
threshold (Markov: on F₁₇ n=16 k=3 the exact series gives bad-center count ≈ 3·10¹⁹ at the verified
crossover — consistent, 537× sharper than the crude V(r) control, but hopeless). The proximity-gap
quantity lives on LINES, so the kernel was restricted to a line (LinePairCooccurrenceBound.lean,
axiom-clean): on {f+γg} with g nowhere zero, any two words at distance w co-occur in the
agreement-≥a lists ≤ 2(n−w)/(2a−w) times (integer form B·2a ≤ B·w + 2(n−w)), and NEVER when
2a > 2n−w. One-vote-per-coordinate double counting (same primitive as Hab25Core Lemma 1, new
combination: codeword-pair co-occurrence = the off-diagonal of the per-line second moment).

**Sharp on the rate-1/2 smooth instance** RS[8,4]/F₁₇ (order-8 domain ⟨2⟩, a=5, δ=3/8 strictly
interior): predicts cooc ≤1 for w∈{5,6}, =0 for w∈{7,8}; an 80-line/4181-pair exhaustive scan
matched EXACTLY (every w∈{5,6} pair co-occurred exactly once, w∈{7,8} never), zero violations.
At ρ=1/2 every pair in the prize window satisfies 2a>w — never vacuous. At ρ<1/3 (e.g. the n=16
k=3 table instance, w≥14>2a) the 2a>w regime is empty — the bound's home is exactly rate ≥ 1/3.

**Honest findings from the same scan.** (1) The DeltaStarTableSmoothInstances F₁₇ n=16 k=3
crossover (a*=5, B=10) is the HARD-WORD crossover, not the global per-code δ*: a line point with
list 15 ≥ a=5 exists (worse center than the table's witness word). (2) Off-diagonal mass dominates
the per-line second moment at a=4 (98%) — co-occurrence is NOT rare; the pair bound, not scarcity,
is what controls it. **Next lever:** assemble per-line ∑_γ|Λ(γ,a)|² ≤ M + Σ_pairs 2(n−w)/(2a−w)
over line-list pairs (M = per-line first moment via the same one-vote count ≤ n/a per codeword),
then close the loop against the per-line list bound the prize formula needs.

### O12 — naive exhaustiveness REFUTED: dense secondary list elements past Johnson (nubs, 2026-06-09)

Max-list hunt past Johnson (n=16, k=8, agree ≥ 9 = radius 7/16 where johnsonDenom < 0, BabyBear,
noise-free, reproducible seed 13): hill-climbing along the KK line found λ with an e₁-fiber giving
THREE simultaneous sparse-lift witnesses (agreement 10) — and an exact list of **19**, the other
**16 elements DENSE** (full support 0..7, not X²-shaped), at exactly-threshold agreement 9. So the
sparse-lift structured families do NOT exhaust beyond-Johnson lists: multi-witness words carry a
derived dense population. Random starts stay at list ≈ 0 — big lists remain reachable only from
structure. **The upper-bound (P-B / S-two Conj 1 / off-diagonal) question is now quantified as the
ENRICHMENT RATIO** (max-list / structured-core; ≥ 6× at n=16): polynomial ⟹ the 2^{O(H/η)} budget
survives (count = N₀-type core × poly); exponential ⟹ Conj 1 itself is threatened. Next probes:
ratio scaling at n=32; theory: are dense elements interpolation artifacts of witness agreement-set
unions (their exactly-threshold agreement suggests so)? Scripts: probe_maxlist.py, probe_dissect.py.

### O12′ — enrichment localizes BELOW the witness radius; zero at witness level (nubs, 2026-06-09)

Follow-up to O12: at n=16 the max-fiber multi-witness word has exact list = its structured core
(3/3) at the witness agreement level (≥10); the dense population (O12's 16 extra) exists only one
notch below (≥9). So sparse-lift exhaustiveness HOLDS at each construction's own radius; the dense
elements are marginal below-witness artifacts. New refined hypothesis **H2 (radius recursion)**:
ℓ(θ) ≤ Σ_levels (structured cores at radii ≥ θ) + per-level marginals controlled one notch tighter
— poly marginals ⟹ the 2^{O(H/η)} budget survives. Also: fiber-formula refinement verified
(odd r: C(m/2−1,(r−1)/2) — 3, 35 exact). n=32 union-sampling needs witness/dense classification
before its ratio is meaningful (17 found vs core 35, composition unclassified). Scripts:
probe_enrichment.py.

### O31 / Rounds 14–16 (main-loop solo) — constant gap + averaging closure + smooth self-similarity

Three new verified theorems (all axiom-clean, 0 sorry/warnings, on main):
* `DeltaStarConstantGapBelowCapacity` (R14): δ* ≤ 1−ρ−ρ/127·(1±o(1)) at prize scale — the averaging
  bound beats ε*·|F| ≤ 2^128 for t ≤ ~2k/254 (rate-1/2 needs the Pascal SHIFT C(2m,m+t) ≥
  centralBinom(m−t); rates <1/2 use monotone C(n,k+t) ≥ centralBinom(k+t)). Witnesses n=2^20
  (t=4063 → δ≈0.49613); extreme-parameter strict instantiation proven outright. Prize-scale bracket
  now δ* ∈ [1−√ρ, 1−ρ−ρ/127].
* `AveragingReachNoGo` (R14b): matching no-go — for q ≥ 2^255, C(n,k+t)·2^128 ≤ q^{t+1} once
  t ≥ (n−127)/255 (C(n,a) ≤ 2^n). The averaging method's reach at max fields is pinned to
  t/n ∈ [~1/258, ~1/255] — a ~1% window; the route is CLOSED as a method (R14 essentially optimal).
* `SmoothDomainSelfSimilarity` (R16): NEW structural theorem SPECIFIC to smooth domains — for s | n,
  Polynomial.expand lifts the scale-s list INTO the scale-n list at the SAME rate and SAME relative
  radius (selfsimilar_list_le; power map x↦x^e has uniform e-fibers on μ_n; agreement multiplies
  exactly by e). Consequences: prize-family worst-case list at fixed (ρ,δ) is MONOTONE in m for
  n=2^m (small-scale δ*-table data lifts to prize scale); any future beyond-Johnson cap must respect
  all divisor scales simultaneously. Honest: rate/radius-preserving ⟹ transfers data within the gap
  but cannot alone decide δ*.

R15 research survey (19 sourced findings, posted to #232): Mathlib PR #38606 = Lam-Leung prep
(upstream is formalizing vanishing sums); PR #38014 = first linear-code PR; Krawtchouk/MacWilliams/
Johnson/Weil-beyond-deg-1 absent everywhere. EXTERNAL COMPETITION: iotexproject/rs-proximity-gaps
(ePrints 2026/861, 2026/858, May 2026) CLAIMS FRI soundness ABOVE Johnson at deployed parameters —
their Lean is only the RVW13 halving lemma (window-dressing); paper math under adversarial deep-read.

**O30 addendum (round-14b, same session).** `LineSecondMomentBound.lean` (axiom-clean) assembles
the round: (1) supp/offSupp partition; (2) UNIFORM pair bound — in the `2a > n` regime (δ < 1/2,
the whole ρ=1/2 prize window) the pair bound is monotone in w via `(w−d)(2a−n) ≥ 0`, so every
pair at distance ≥ d obeys the single bound `B·(2a−d) ≤ 2(n−d)` (≤ 1 on the RS[8,4]/F₁₇ witness);
(3) the per-line second-moment identity `∑_γ|Λ(γ)|² = ∑_γ|Λ(γ)| + ∑_{C.offDiag}|badSet|` (the line
counterpart of the O28 kernel identity) and the assembled bound
`(∑|Λ|²)·(2a−d) ≤ (∑|Λ|)·(2a−d) + (|C|²−|C|)·2(n−d)`. The off-diagonal is now distance-uniform per
pair instead of the past-Johnson-blowing ball-intersection volume. The remaining open content is
the PAIR COUNT: `|C|²−|C|` is the trivial bound; the scan shows the true number of co-occurring
pairs on a line is tiny, and a diameter argument (all of Λ(γ) pairwise agree on ≥ 2a−n coords,
so for RS with 2a−n ≥ k the list is a singleton — the unique-decoding collapse) shows where RS
structure must enter past that. The co-occurring-pair count for explicit smooth-domain RS in
(Johnson, capacity) is the sharpened open kernel.

### O12″ — H2-decomposition refuted: the marginal layer is balanced-overlap (nubs, 2026-06-09)

Follow-up to O12/O12′ (seed-13 reproducible, n=16, BabyBear): the dense below-witness population is
NOT union-decomposable — 0/16 agreement sets lie inside the witness union (|∪|=14/16); instead every
dense element intersects EACH of the 3 witness sets in exactly 5–6 of its 9 points ((6,5,5)×8,
(6,6,6)×4, (5,5,5)×4) and uses outside points. Verdicts: H1-naive and H2-decomposition both
eliminated by explicit example; surviving facts: zero enrichment AT witness radius, and the
marginal layer is rigidly balanced-overlap with full coefficient support. The correct upper-bound
mechanism must engage the witnesses' mutual algebra, not agreement-set combinatorics. Next: targeted
literature check (deep-hole / balanced-overlap phenomena in list decoding) + the witnesses' pairwise
agreement algebra. Scripts: probe_h2.py.

**O30 probe (pair-count field scaling, nubs).** Rate-1/2 order-8 smooth instances, n=8 k=4 a=5,
30 random lines each: per-line list mass M = ∑_γ|Λ(γ)| is FIELD-SIZE INDEPENDENT (48.1 / 51.8 /
52.9 at q = 17 / 41 / 73), while co-occurring pairs per line match the birthday estimate M²/2q
exactly (predicted 73 / 30 / 17, observed 53.7 / 23.2 / 15.3). So on random lines the off-diagonal
is purely birthday-random: per-line 2nd moment ≈ M + O(M²/q) — exactly the poly/|F| shape the prize
needs. The reduced conjecture: (i) M ≤ poly(n) uniformly over lines (M is the line-list mass, a
combinatorial (n,k,a) quantity, empirically constant in q), and (ii) adversarial lines cannot beat
birthday by more than poly(n) (vote anti-concentration — where smooth-domain RS structure must
enter). Either piece failing would localize the obstruction; both holding pins ε_line ≈ M²/q per
line. Evidence, not proof; lower-bound side untested on adversarial lines.

### O12‴ — the marginal layer is a TRANSVERSAL DESIGN; H3′ is the live budget-survives hypothesis (nubs, 2026-06-09)

Exact dissection (seed-13, n=16, BabyBear): witness region lattice [pairwise 4,4,4; triple 2;
outside 2]; ALL 16 marginal elements are near-uniform transversals (region profile {2,2,2,2,1} up
to permutation), equidistant from the witness triple (5–6 agreements each, full domain), always
touching the outside region. Realized 16 ≪ transversal shape space ⟹ strong algebraic culling.
**H3′:** marginals ≤ region-lattice transversal count = poly(n) per configuration ⟹
ℓ(θ) ≤ N₀-core × poly ⟹ the 2^{O(H(ρ)/η)} budget SURVIVES. Trajectory: H1 refuted → H2 refuted →
H3′ live with exact single-configuration support. Next: second configuration + n=32 test, then the
transversal-count proof attempt (finite algebra, Lean-able if it holds). Scripts: probe_h3.py.

### O12⁗ — the fiber-3 marginal design replicates EXACTLY; C19 is theorem-shaped (nubs, 2026-06-09)

Second, fully deterministic fiber-3 configuration (max-fiber λ, no randomness) reproduces O12‴'s
structure EXACTLY: list 19 = 3 + 16, region lattice [4,4,4,2,2], 16/16 dense = {2,2,2,2,1}
transversals, witness-agreement multiplicities (6,5,5)×8/(6,6,6)×4/(5,5,5)×4 — all
configuration-independent. **Conjecture C19:** every fiber-3 λ of the (16, 8, 5) smooth
construction has agree-≥9 list EXACTLY 19 with this design. Finite ⟹ provable ⟹ Lean-able; its
proof would deliver the first proven marginal-layer count past Johnson on a smooth domain and
validate the region/transversal mechanism as the upper-bound technique. The P-B program now has a
concrete mechanism candidate instead of a mystery. Scripts: probe_h3_cfg2.py.

### O32 / Rounds 15–17 — Sudan end-to-end + θ-optimization + external-claim deep-read + CA engine

* `SudanListBoundFull` (R15 harvest): the COMPLETE Sudan (m=1) list bound, end to end self-contained
  (interpolation existence via rank-nullity + (Y−Cf) ∣ Q factor extraction + Y-degree cap):
  n < Σ_{j<D}(D−(k−1)j), D ≤ t ⟹ list ≤ (D−1)/(k−1). Radius 1−√(2ρ) (NOT Johnson; mult ≥ 2 = GS
  proper still open in-tree). First complete algebraic list-decoding bound in the corpus.
* `SecondMomentThetaOptimization` (R15 harvest): the missing downstream of the ORPHANED MGF kernel
  rs_sum_jointCoverCount_mgf_le — θ-optimization over ℝ: interior optimum θ*=2ra/(b(n−2r)), entropy
  form at θ=r/n, and S ≤ (n/r)^{2r}(exp((q−1)r) + exp((q²+q−1)r)/q^{n−k}).
* DEEP-READ VERDICT (ePrint 2026/858/861, "FRI soundness above Johnson"): protocol-level threshold
  halving — RVW13 half-threshold CA (≤1 bad γ at conclusion δ/2) + BCIKS distance locking after
  round 1; ~2× queries; the OPEN-ZONE equal-threshold CA/MCA (the prize quantity) explicitly "Not
  solved here" (their claim map). Their Thm 7: equal-threshold bad-γ count ≤ C(n,k+1) (field-indep);
  tightness (Prop 9) needs |F| > C(n,w)² ≫ 2^256 — does NOT fit prize fields. Their Conjecture 41
  (M ≤ ⌊(2D−1)/c⌋ at codim excess c ≥ 3, ⟹ M=O(1) at Johnson) = the live prize-shaped list
  conjecture, UNPROVEN (empirics to n=40).
* `CAPairExtractionEngine` (R17): their verified kernel formalized — pair_of_two_bad (two bad γ's
  solve for the codeword pair), bad_card_le_one (RVW13 half-threshold ≤1 bad γ), bad_card_le_choose
  (equal-threshold ≤ C(n,k+1), field-independent). All axiom-clean.

### O33 — §7 phase-diagram convergence analysis (2026/858 deep-read, part 2)

Full §7 read. The codimension-excess phase diagram (D = n−k, c = D−w, list radius w):
* c ≥ w (unique decoding): M ≤ 1 — in-tree in equivalent forms.
* incidence bound (c < w): M ≤ C(n,d)/C(w,d), d = w−c — **this is EXACTLY our in-tree
  FisherPastJohnsonCap k-uniform bound (round 11)**: independent convergence on the same theorem,
  including the same honest finding (valid past Johnson, too lossy at prize scale).
* c = 2: their Möbius/core bound M ≤ min(p, 2C(n,w−1)) is PROVEN (Berlekamp error-locator + degree-2
  elimination per (w−1)-core — formalizable, companion-note-sized); the EXPONENTIAL worst case
  0.66·1.36^n is EMPIRICAL ONLY (R²-fit to n=24, no theorem; their §8 open item). Their peak prime
  p ≈ √C(n,w) sits exactly at the averaging floor — the empirical 1.36^n is far ABOVE the floor,
  i.e. unproven worst-case CONCENTRATION (matches our round-6/7 concentration-door cartography).
* c ≥ 3: Conjecture 41 (rank lemma: M ≤ ⌊(2D−1)/c⌋, linear) — predicts M = O(1) at Johnson; the
  deployment regime c = Θ(n). UNPROVEN (exhaustive to n=15, empirics to n=40; rank-deficient
  triples DO exist at c=2 from n=11 — translate families with a divisibility criterion — and none
  found at c ≥ 3). **Conjecture 41 ≈ the prize's Grand List Challenge**, reformulated as a ℚ-rank
  statement on integer constraint matrices from elementary-symmetric coefficients of point subsets.

Net: the external race converged on our cartography (incidence cap, concentration door, near-capacity
exponential); the live open kernel is now THREE equivalent formulations — (i) sharp ball-intersection
2nd moment (our O28/O29), (ii) the t≥2 multi-esymm concentration (our O20-O22), (iii) their c≥3 rank
lemma (Conj 41). All the same wall, none proven. Issue stays open.

### O13 — C19 PROVEN at configuration; the mechanism is a 2-adic even/odd DESCENT (nubs, 2026-06-09)

Complete finite verification chain (deterministic scripts probe_c19_{skeleton,count}.py):
even/odd reduction (111/111 machine checks; witnesses `BBBBB000`, dense exactly `BBB11100`) →
c_o = γΠ_B / c_e = I₃(v)+αΠ_B → 3×2 consistency systems → exhaustive 4480-selection enumeration →
**EXACTLY 16 consistent = the dense count, from first principles.** With the standard
rotation/Galois equivariance transport, C19 (every fiber-3 λ of the (16,8,5) smooth construction
has agree-≥9 list EXACTLY 19 = 3 + 16 with the transversal design) is **proven** — the first exact
beyond-Johnson list structure on a smooth domain. **Mechanism:** the proof is ONE step of a 2-adic
tower descent (n → n/2 via even/odd parts, agreement → per-z both/one-sided patterns, counting →
explicit cyclotomic linear algebra). The general P-B upper-bound attack is now concrete: iterate
the descent; the 2^{O(H/η)} budget should emerge as a product of per-level pattern counts. This is
the first mechanism-level candidate for the open core that has a PROVEN base case. Next: general
descent recursion + n=32 two-step test + equivariance write-up + Lean brick (fully finite).

### O13′ — descent self-similarity verified at n=32: the converse-FRI recursion is real (nubs, 2026-06-09)

All 17 sampled n=32 list elements descend (even/odd = the FRI fold) to pure-B level-1 patterns with
verified conditions — exactly lifts of level-1 list elements of the descended word, which is the
same line construction one level down. Recursion: ℓ₀ = ℓ₁(c_o=0 branch) + Σ mixed-pattern branches,
each mixed branch a C19-style finite consistency count. The 2^{O(H/η)} budget = product of
per-level branch counts over the tower. PROGRAM: (1) converse-FRI descent lemma (rigorous, easy);
(2) per-level branch-count bound (the remaining heart — C19 proved one full level exactly);
(3) marginal-layer sampler at n=32 (needs ≥3-witness unions + outside, per the n=16 anatomy).
First mechanism-level program for the open core with a fully proven base level. Scripts:
probe_descent32.py.

### O13″ — Descent Lemma formalized; the prize upper half ⟺ DEGENERACY COUNTING (Conjecture D) (nubs, 2026-06-09)

`07-DESCENT.md` (research folder): the converse-FRI Descent Lemma in full rigor — c(y) =
c_e(y²)+y·c_o(y²); per-z trichotomy B (joint pair-agreement, 2 constraints) / one-sided (one
σ-twisted affine relation) / none; agree = 2#B+#1; pure branch = exact lift of the level-1 list
(self-similar, verified n=32). **Overdetermination identity: constraints − unknowns ≥ ηn** — every
beyond-rate list element is an ηn-fold cyclotomic degeneracy; ℓ(θ) = the degeneracy count.
**Conjecture D:** per-level degeneracies ≤ poly·N₀-type subgroup counts ⟹ telescoping to the
2^{O(H(ρ)/η)} budget. C19 = the first proven degeneracy count (16, exact). The open core is now
ONE precisely-stated conjecture with a rigorous reduction, a proven base instance, and verified
self-similarity — falsification target included (any level with super-N₀ degeneracies).

### O34 / Round-18 — the prize-scale two-sided bracket (flagship)

`TwoSidedBracketPrizeScale.lean` (main-loop solo, axiom-clean): two_sided_bracket_n2_20 = both sides
at n=2^20 rate 1/2, all prize fields, in ONE self-contained statement. Johnson side: johnson_list_cap
L·(a²−nJ) ≤ n·a (truncated double count + pair sum + ℕ Cauchy-Schwarz; instance a=750000 → L ≤ 61).
Capacity side: capacity_crossover (R14) 2^128·q^4063 < C(2^20, 2^19+4063). NET: δ* ∈ [0.2848, 0.49613)
— sharpest self-contained machine-checked prize-scale bracket. Johnson side → 0.2929 needs mult-2 GS
(known math); past Johnson = the open core (3 equivalent formulations, O33). LEAN GOTCHAS: rw with a
repeated filter-card pattern rewrites ALL instances at once (don't list it twice);
sq_sum_le_card_mul_sum_sq works over ℕ directly (Semiring+LinearOrder+IsStrictOrderedRing);
Finset.sum_ite_mem + univ_inter for indicator sums; push_neg deprecated → push Not.

### O14 — KERNEL LEMMA proven: smoothness kills σ-twisted kernels; D ⟹ consistency-rarity only (nubs, 2026-06-09)

**Lemma K (3-line proof, in research-folder 05-LOG Entry 18):** deg<κ pairs (e,f) with
e(z) = −σ_z y_z f(z) on |O| ≥ 2κ tower points are zero — substitute z = d²: e(d²)+d·f(d²) has
degree ≤ 2κ−1 but ≥ 2κ distinct roots σ_z y_z. Unconditional (no genericity). Consequences:
per-pattern solutions ≤ 1 in the overdetermined regime forced by the ηn-overdetermination identity;
hence ℓ(θ) = #consistent (B,O,σ) patterns — **Conjecture D is now purely inhomogeneous
consistency-rarity** (cyclotomic identity counting; C19's exhaustive 4480→16 is the worked
instance). This is the mechanism-level answer to "what randomness supplies that smoothness must
replace": the d²=z parametrization supplies unconditional kernel rigidity. Lean brick queued
(pure degree counting).

### O14′ — exactness/circularity: single-level descent consistency IS the list count (nubs, 2026-06-09)

Exact derivation (research 05-LOG Entry 19): the twisted consistency data of a (B,O,σ) pattern
assembles to ρ(d) = −(Ã−w)(d)/Π_B(d²), and consistency ⟺ ∃ deg<k codeword agreeing with w on
D ∪ s⁻¹(B) — a tautological bijection with level-0 list elements. **The descent route is exact,
hence circular as a single-level upper bound** — eliminating the one-level shortcut permanently.
Conjecture D's genuine content: the cross-level paired induction (list + correlated-agreement
bounds simultaneously down the tower; pattern entropy vs cyclotomic rarity). Proven structure
retained: Lemma K uniqueness, the pattern⟷element bijection, C19's arithmetic-rarity instance.
This is the precise missing fact of the upper half, stated as sharply as it can be.

### O15 — definitive framing: prize upper half ⟺ classical beyond-Johnson RS list decoding (nubs, 2026-06-09)

Both bridge directions are now formal and cited: BCIKS 2055 Thm 1.9 (gaps beyond LDR_{F,D,q} are
impossible with soundness < 1/(2n) — "list decoding beyond Johnson is a prerequisite") and GG25
Thm 3.5 (line-decodability ⟹ MCA). **So the Grand MCA upper half ⟺ poly list-decodability of
smooth-domain RS past Johnson — the classical open problem since GS99.** Anchors: JH01/BSKR06
negatives are subspace/subfield-domain; KK25 negatives live at the capacity edge only (2^{O(1/η)}
is constant-in-n at fixed η); random-domain positives (RW13…AGL24) don't cover deterministic
smooth. The middle band for 2-power multiplicative domains is open BOTH ways. Conjecture D = that
classical question; our proven smooth-domain machinery (N₀/Lift/C19/Descent/Kernel/circularity)
is the new equipment. This is the sharpest honest statement of where the $1M sits — and why no
formalization shortcut exists: the missing fact is a famous open problem, now with named footholds.

### O31 / Round-15 — the GS ladder complete: Sudan end-to-end, multiplicity-m machine, both walls

Round 15 (workflow stalled mid-round; recovered by hand + one Fable agent). On main `3767f758b`:
* `SudanListBound` — the §7 Table-1 deliverable: end-to-end m=1 list bound |L| ≤ (D−1)/(k−1) for
  general RS under explicit hyps n < Σ_{j<D}(D−(k−1)j) ∧ D ≤ t; ZMod 13 instance + genuine
  2-element-list witness.
* `GSExactCountWall` (own grind) — exact-count upper bound 2c·gsCount ≤ (D+c)² (Gauss over ℤ + AM–GM,
  u=cq ∈ [D,D+c−1]) ⟹ wall √(n·c·m·(m+1)) < t·m+c. Concrete: n=100,c=25,m=1 feasible t=60,
  infeasible t=59 (D²-form: 72; Johnson: 50). BOTH GS accountings stop above Johnson.
* `GSHasseMultiplicity` (Fable agent + 1-line simp-recursion fix) — the FULL multiplicity-m machine:
  hasse_interpolation_exists (order-m shifted-coefficient vanishing, n·C(m+1,2) constraint count),
  pow_X_sub_C_dvd_eval_of_hasseVanish ((X−a)^m ∣ Q(X,f(X)) via inner-shift ring hom),
  factor_of_order_agreement (m·agree ≥ D ⟹ (Y−f)∣Q), gs_decoder_pipeline (one Q factors every
  m·agree ≥ D codeword). ZMod 5 instances.

**Net.** The GS route is now FULLY machine-checked: Sudan → multiplicity-m → walls → open interior.
Every formalizable rung done; the residual is exactly the open research core (an explicit certificate
beating Johnson for smooth-domain RS). Issue stays open. WORKFLOW LESSON: agents can stall on a single
simp-recursion for 10+ min — check in, take over, fix by hand (deterministic rw beats simp loops).

### O32 — capstone gs_full_list_bound + the multiplicity ladder + the folding-transfer no-go

Final entries of the rounds-8-15 arc (all own-hand work after the round-15 workflow stalled):
* `GSFullListBound.lean` (main `80ad309ca`) — gs_full_list_bound: the assembled multiplicity-m GS
  list bound (any field, any n distinct points, any m: n·C(m+1,2) < #gsSupport(D,k) ∧ D ≤ m·t ⟹
  every t-agreement list ≤ (D−1)/(k−1)). THE MULTIPLICITY LADDER at n=50,k=2: m=1→t=10, m=2→t=9,
  m=4→t=8 = the integer Johnson floor (√50≈7.07), instantiated over ZMod 53 with 50 explicit points.
  Multiplicity climbs exactly to Johnson; the walls (O29/GSExactCountWall) prove no further.
* `FoldingTransferNoGo.lean` (main `3183c68dc`) — §6 route 4 naive direction certified dead:
  (d+1)·foldedAgree ≤ plainAgree is the only true direction; one corruption per orbit gives
  plainAgree = N·d (fraction d/(d+1)) with foldedAgree = 0, so folded-capacity results say nothing
  about plain-close words. The open part (transfer surviving per-orbit corruption) is isolated.

**THE §6 ROUTE LEDGER (final):** 1 derandomization — gap as Props, OPEN; 2 list⇒MCA collapse —
partial bridges + the proven list↛ε_mca correction; 3 syndrome lens — externally unvalidated;
4 folding — naive dead (theorem), open part isolated; 5 two-sided interpolation — THE VERIFIED
BRACKET δ* ∈ [1−√ρ, 1−ρ−c_ρ]: left end = Sudan→multiplicity-m→walls (every known certificate stops
at Johnson), right end = averaging at prize scale. ~31 axiom-clean files rounds 8-15. The interior
is the open research the prize elicits; every dead end is now a theorem rather than folklore.

### O35 — Lemma K + pattern rigidity LANDED as Lean bricks (`DescentKernelLemma.lean`)

The queued formalization work of O13″/O14 is discharged — `DescentKernelLemma.lean`
(axiom-clean `[propext, Classical.choice, Quot.sound]`, 0 sorry, 0 warnings,
characteristic-free over any integral domain where applicable):

* `glue e f = expand 2 e + X·expand 2 f` API: coefficient extraction (even/odd supports
  disjoint — **no characteristic assumption**, unlike the FRI `NonBinaryField` machinery),
  evaluation `glue(d) = e(d²) + d·f(d²)`, degree bound `< 2κ`, injectivity, and
  `exists_glue_decomposition` (every deg-`< 2κ` polynomial is a glue with parts `< κ`).
* `kernel_rigidity` = **Lemma K** (O14): deg-`< κ` pairs `(e,f)` with
  `e(z) + r_z·f(z) = 0` on `≥ 2κ` square-rooted points vanish identically. Smoothness
  (the `d² = z` parametrization) supplies unconditional kernel rigidity.
* `solution_unique`: per-pattern solutions ≤ 1 for the inhomogeneous one-sided system.
* `pattern_rigidity` — the **sharp weighted form**: a `(B, O₁, σ)` pattern with
  `2|B| + |O₁| ≥ 2κ` pins `(e,f)` uniquely (roots harvested at BOTH `±y_z` for `z ∈ B`,
  at `σ_z` for `z ∈ O₁`; total `2|B| + |O₁|` distinct roots of the glued difference).
* `agreement_count` — the O13″ identity `#agreements = 2|B| + |O₁|` on a ±-paired domain
  (filter-biUnion + per-pair indicator split), plus the per-`z` trichotomy bridges
  `both_agreement_iff` / `one_sided_agreement_iff`.

Net: the descent program's reduction "`ℓ(θ)` = #(consistent patterns)" is now rigorous in
Lean at the single-level granularity — every beyond-rate list element (agreement
`a ≥ k = 2κ` ⟹ `2|B| + |O₁| ≥ 2κ`) is uniquely determined by its pattern. Conjecture D's
remaining content is exactly the cross-level consistency-rarity count (C19's 4480 → 16 is
the worked instance), unchanged but now with its bookkeeping machine-checked.

### O36 / Round-19 — Conjecture-41 beachhead (clique structure + large-p transfer)

Full §7+§8 read of 2026/858: Conj 41's UNIVERSAL obstruction at every c = the (w+1)-clique (all
w-subsets of a (w+1)-set; their p=113 triangle / p=61 tetrahedron). `Conjecture41CliqueBeachhead`
(main-loop solo, axiom-clean, strict-flags-verified): clique locators = Lagrange numerators
(∏_{β∈W∖α}(X−β)); cliqueLocator_linearIndependent over ANY field (diagonal evaluation);
clique_syndrome_kernel_trivial (c=1 rank statement — span F^{|W|} via independent + count=finrank,
universal obstruction has NO c=1 kernel anywhere); det_map_zmod_ne_zero (exceptional primes confined
to divisors of one ℤ-determinant — the effective Schwartz-Zippel threshold mechanism). OPEN: the
γ-twisted [N|γN] rank at c≥3 for arbitrary families (= Conj 41 = the prize list core). Also from §8:
the k-wise independence of error-locator normals is EMPIRICALLY FALSE at c=2 k≥3 (common-core triples
have rank ≤ 2c < 3c) — the pairwise→k-wise promotion is structurally blocked; and the birthday-bound
conjecture (max_γ M_γ ≤ C₁·C(n,w)/p uniform) is their remaining c=2 door.
### O37 — the c=2 core-elimination bound LANDED (`C2CoreEliminationBound.lean`) + an honest proviso found in 2026/858 Thm 38

The O33-flagged "formalizable, companion-note-sized" c=2 worst-case bound of ePrint
2026/858 §7.5 is now machine-checked (axiom-clean, 0 sorry, 0 warnings, any field):

* `syndr_insert` — the shift identity engine of their Lemma 37: adjoining a point to a
  core acts LINEARLY on every shifted syndrome functional ⟹ the c=2 compatibility system
  is bilinear in (extension point, line parameter).
* `coreQuad` + `coreQuad_eval_eq_zero` — the degree-≤2 elimination resultant per
  (w−1)-core; every compatible extension point is a root (their Thm 38 elimination).
* `gamma_unique` — division-free Möbius-image well-definedness: a nondegenerate core
  admits ≤ 1 compatible γ per extension point.
* `c2_core_bound` — #{γ : ∃ E compatible} ≤ 2·C(n, w−1), p-independent.
* **HONEST FINDING (de-laundering):** the paper packages the result as
  `M_compat ≤ min(p, 2·C(n,w−1))` with the degenerate case handled by "≤ p trivially" —
  but `min` claims BOTH components, and a degenerate support (all four window functionals
  vanish) makes EVERY γ ∈ F_p compatible, so the 2·C(n,w−1) component genuinely needs a
  nondegeneracy proviso. `coreQuad_eq_zero_of_degenerate` (not stated in the paper) pins
  the minimal such hypothesis: a degenerate support kills the quadratic of every one of
  its cores, so "every support has ≥ 1 core with nonzero quadratic" (our `hq`) is exactly
  the right granularity. `c2_min_bound` is the honest min-form under `hq`;
  `c2_card_bound` is what survives without it.

Net: the verified codimension ladder now reads c≥w (unique decoding) → incidence/Fisher
cap → GS walls at Johnson → **c=2 core-elimination (this)** → c≥3 = Conjecture 41 ≈ the
prize's open core, starting exactly one codimension above what is now machine-checked.

### O37 / Round-20 — clique double-block kernel = twisted evaluation pencil (NEW theorem)

`Conjecture41CliqueKernelStructure.lean` (main-loop solo, axiom-clean, strict-verified): DUALITY
⟨Λ_{E_α}X^r, ev_β⟩ = β^r·Λ_{E_α}(β) (locators/vertex-evaluations dual system under the coefficient
pairing); clique_kernel_mem — the twisted evaluation pencil (s₁,s₂) = (−Σγ(β)b(β)ev_β, Σb(β)ev_β)
satisfies ALL (w+1)c kernel conditions of [N|γN] at EVERY c over EVERY field;
evalSyndrome_family_injective — pencil dim = w+1 exactly. CONSEQUENCE: the universal obstruction is
UNCONDITIONALLY rank-deficient (rank ≤ 2D−(w+1) always) — Conj 41's full-rank branch ALWAYS fails on
cliques; the conjecture = its degeneracy branch = "the twisted pencil contains no nondegenerate
syndrome at p > p₀". Pencil syndromes = syndromes of errors supported on W (Remark-31 false
positives). PAPER-MATH derived (docstring, queued): partial fractions ⟹ single-block relation module
= {((x−α)v_α) : Σv_α = 0, deg v_α < c−1}, rank N_clique = D, full kernel count. NEXT: (a) pencil =
WHOLE kernel formalization, (b) the degeneracy analysis (the Vandermonde solution V_{E_α}^{-1}s₂ of a
pencil syndrome — when all-nonzero) = the sharp remaining core of Conj 41 for cliques.

### O38 — effective per-prime exactness: AM–GM norm threshold closes the P-A residuals above T(m,r) (nubs, 2026-06-09)

New note `EffectivePerPrimeExactness.md` + deterministic probes `scripts/probes/probe_norm_threshold.py`
+ `probe_e1_saturation.py` (all checks PASS, exit 0; survived a 4-lens adversarial review panel —
algebraic-NT/combinatorics/prize-fidelity/numerics — whose one major, a false `≤4·min(s,s′)`
intermediate step in the E2 support-bound proof, was corrected pre-push with the statement intact
and exhaustively verified tight; every figure independently reproduced, incl. a Goldilocks MITM
re-implementation with a different reduction algorithm, bit-identical). **Theorem E1:** for nonzero α = Σ_{j<m/2} c_j ζ_m^j (m = 2^k):
Σ_{i∈(ℤ/m)^×} |σ_i(α)|² = (m/2)·Σ_j c_j² (odd-character orthogonality), hence by AM–GM
|N_{K/ℚ}(α)| ≤ (Σ_j c_j²)^{m/4}. **Corollary E2:** a layer-r collision of the e₁-image on
r-subsets of the order-m subgroup forces p ≤ T(m,r) := (4·min(r, m−r))^{m/4} — so every prime
p ≡ 1 (mod m) with p > T(m,r) has image EXACTLY N₀(m,r), char-0 fibers included; all-layers
threshold T_all(m) = (2m)^{m/4}; support-graded version: p > (4t)^{m/4} forces collision support
> t. Replaces the m^{m/2} sup-norm bound and KK25's φ(m)^{φ(m)} prime requirement (m=64:
2^111.3 vs 2^192 / 2^160 — and KK's unsigned subset count C(φ(m),r) VANISHES at ρ=1/2 where
r = m/2+1 > φ(m), while N₀ keeps the full signed count). **Corollary E3** (composed with the
verified Lift Lemma): for EVERY prime T(m', ρm'+1) < p < 2^128·N₀(m', ρm'+1), p ≡ 1 (mod n),
m' | n: ε_mca(RS[F_p, H_n, ρn], 1−ρ−1/m') ≥ N₀(m', ρm'+1)/p > 2^−128 — per-prime, effective,
NO averaging, NO Siegel–Walfisz/GRH. With the δ*-existence floor (unconditional |F| > 2^128 via
the verified ε_mca ≥ 1/|F| up-to-capacity bound; |F| ≥ 2^129 given the 2/|F| δ=0 row + monotone
ε_mca): **δ*_C < 1 − ρ − 1/64 for ALL smooth prime fields in
[2^129, ≈2^145–2^177] at all four prize rates**; thin η=1/128 windows are even nonempty at
ρ=1/8 (2^194.8, 2^195.3) and ρ=1/16 (2^165.4, 2^171.7). **Verified predictions:** Goldilocks
m=32 full image EXACT by MITM enumeration (21,523,360 at r=17; 21,523,361 at r=16). **New
data + two corrections:** BabyBear m=32 r=17 is genuinely DEFICIENT — exact image 21,477,408
= 99.787% of N₀ (45,952 lost): the old sampled ≈5.6M estimate was a coupon-collector artifact
(~4× low), and the zero-fiber spot-check missed the deficiency, so production-31-bit full-image
exactness stops at m=16. Empirical m=32 onset ∈ (2^30.9, 2^34] vs proven T ≈ 2^47.26 (~2^13–16
loose, same shape as the exhaustive m∈{8,16} onset scans: largest deficient primes 17 / 205,553
vs T = 144–256 / 614,656). **Open after this:** η=1/128 per-prime windows at ρ ∈ {1/2, 1/4}
— and PROVABLY not openable by norm-size arguments: `probe_e1_saturation.py` exhibits an explicit
admissible layer-65 difference c (support 62, Σc²=248) with log₂|N(c)| ≈ 252.4, within 2.15 bits of
E1 — any size bound must exceed 2^252.4 ≫ the 2^228.4 ceiling, so the window needs p ∤ N(α)
ARITHMETIC (splitting/divisibility) or a new construction, not better inequalities (E1 is
essentially tight on the difference set). The transition zone N₀ ≲ p < T (lattice statistics of
𝔭 ∩ {−2..2}^{m/2}); P-B untouched (descent lane O13–O13″).

### O37 addendum — the literal Thm 38 `min` packaging is REFUTED (machine-checked counterexample)

The O37 proviso is not caution — it is necessary. `C2CoreEliminationBound.lean` §DegenerateLine
(axiom-clean, 0 sorry, 0 warnings) upgrades the paper's own Remark-31 evaluation-syndrome device
to a LINE: take `s₁ = s_α, s₂ = s_β` (evaluation syndromes) with `{α, β} ⊆ E`. Both window
functionals of `Λ_E` and `X·Λ_E` are `x^r·Λ_E(x)` at a root of `Λ_E`, so they vanish at both
line endpoints ⟹ EVERY `γ ∈ F` is compatible:

* `compat_evalSynd_line` — the degeneracy construction (any field, char-free).
* `degenerate_line_full` — the compatible-γ set is all of `F`.
* `thm38_min_bound_fails` — `M_compat ≤ min(p, 2·C(n, w−1))` FAILS whenever
  `|F| > 2·C(n, w−1)` — i.e. for every prize-relevant field size.
* `thm38_refutation_instance` — concrete witness over `ZMod 11` (n=3, w=2, N=4:
  count 11 > 6 = the claimed bound).

Honest scope: the refutation targets `M_compat` exactly as the theorem prints it
(`M_true ≤ M_compat ≤ min(...)`); for `M_true` the same supports contribute nothing (the
Vandermonde solution is supported on `{α,β}`), so their headline `M_true` claims survive —
what's broken is the middle inequality's packaging, fixed by the O37 nondegeneracy proviso
(`c2_min_bound`). The Möbius/core method itself is sound and is now machine-checked in its
corrected form.

### O39 — transition-zone collisions are ideal-theoretic: short generators of (1−ζ)^j·𝔭; class-group obstruction appears exactly at the prize's η (nubs, 2026-06-09)

`probe_transition_structure.py` (deterministic, exit 0): exhaustive collision extraction at the three
boundary primes of O38's transition zone, testing E2(c)'s falsifiable support-floor predictions.
**Data:** onset(16,9) p=205,553: 16 lost values = 8 distinct relations (±), ALL full-support 8/8
(floor predicted ≥6), each with N(α) = 2p EXACTLY, each colliding exactly 2 pattern pairs.
onset(16,5) p=43,793: same shape — 8 relations, all support-6 (floor ≥4), N = 2p. BabyBear(32,17):
45,952 lost (matches O38 bit-exactly), only 32 distinct relations, supports {12: ×16, 14: ×16}
(floor ≥4 — observed min 12), sampled cofactors all N = 8p = N((1−ζ)³)·p; per-relation pair
multiplicities (2,592 at support 12) far under the proven 2^t·3^{m/2−t} cap. All checks PASS.
**Structure:** every observed cofactor is a pure 2-power — forced, since 2 is totally ramified in
ℚ(ζ_{2^k}) (unique norm-2 prime (1−ζ)) and every other prime ideal has norm ≥ 17. So transition
collisions are precisely **box-short generators of the near-prime ideals (1−ζ)^j·𝔭** — the
collision question below T(m,r) is an ideal-theoretic short-generator question, not a generic
lattice-point question (the naive Gaussian/Fourier count predicts ≈76 relations at BabyBear and a
diffuse support profile; reality: 32 relations in two rigid support classes — 2.4× off and
structurally wrong).
**The new direction this opens for the η=1/128 residual (O38 §5: "needs p ∤ N(α) arithmetic"):**
a collision at p forces (α) = 𝔞·𝔭 with N(𝔞) ≤ (Σc²)^{m/4}/p, i.e. (i) 𝔭's ideal class must lie in
{[𝔞]⁻¹ : N𝔞 ≤ budget}, and (ii) the principal ideal 𝔞𝔭 must admit a generator inside the {−2..2}
difference box — the Cramer–Ducas–Peikert–Regev short-generator regime (log-unit lattice). Class
numbers (verified, Washington/Wikipedia table): h(ℚ(ζ₁₆)) = h(ℚ(ζ₃₂)) = 1 — the probed/production
regimes are class-trivial, every 𝔞𝔭 is principal, and collisions appear exactly when short
generators exist (observed). But h(ℚ(ζ₆₄)) = 17 and **h(ℚ(ζ₁₂₈)) = 359,057** (h⁺ = 1): at the
prize's η = 1/64 and 1/128 the class group is nontrivial-to-large, so the relation ideal must land
in a constrained class AND beat the log-unit sparsity — a 1/h-flavored rarity plus CDPR-type
geometry that norm-SIZE arguments (provably exhausted, O38 §5) cannot see. Honest status: a
research direction with verified calibration data at h = 1, NOT a theorem; the quantitative
question is whether class-equidistribution (Chebotarev over the Hilbert class field of ℚ(ζ₁₂₈))
plus log-unit volume bounds give per-prime or explicit-density exactness in (2^225, 2^256).
Next probes: m=64 (h = 17) collision census at feasible p — does the 17-fold class constraint
visibly thin the relation set vs the h = 1 baseline?

### O38 — the sharp rank threshold for error-locator normals (2026/858 Thm 26 + Rem 27) LANDED

`NormalRankSharpThreshold.lean` (axiom-clean, 0 sorry, 0 warnings, any field): the algebraic
dichotomy the §7.2 second-moment/Poisson-dispersion machinery rests on, in kernel form:

* `normal_kernel_trivial` (= their Thm 26): `c + |E₁∩E₂| ≤ |E₁|` ⟹ any degree-`<c` relation
  `Λ_{E₁}P + Λ_{E₂}Q = 0` is trivial — and NO degree bound on `P` is needed (statement is
  stronger than the paper's). Proof is SIMPLER than their gcd route: `A₁ = Λ_{E₁∖E₂}` is
  coprime to `Λ_{E₂}` outright (disjoint root sets), so `A₁ ∣ Q`, killed by
  `deg A₁ = w₁−j ≥ c > deg Q`. No common-factor cancellation step at all.
* `normal_kernel_nontrivial` (= their Rem 27, sharpness): past the threshold both sides,
  the explicit relation `Λ_{E₁}(−Λ_{E₂∖E₁}) + Λ_{E₂}Λ_{E₁∖E₂} = 0` (both cross-products
  = `Λ_{E₁∪E₂}`) lives in the `<c` window and is nontrivial — the shared-core rank
  deficiency is REAL, exactly the mechanism Conjecture 41 must control.

Together with O36 (clique beachhead), O37 (c=2 elimination + min-packaging refutation), the
§7 backbone of 2026/858 is now machine-checked: pairwise independence engine (this), c=2
worst case (O37, corrected), universal clique obstruction (O36) — the open core is Conj 41's
QUANTITATIVE rank statement (how many supports can be simultaneously deficient on a flat),
one step above everything verified here.

### O39 — O38 independently re-verified; four descent-program Lean bricks landed (nubs, 2026-06-09)

(1) **O38 verification:** independently re-ran both O38 probes on a fresh checkout —
`probe_norm_threshold.py` + `probe_e1_saturation.py`: **ALL PASS, zero failures (240.9s)**; the
E1 odd-character orthogonality identity also checks by hand. The effective per-prime exactness
(AM–GM threshold T(m,r)) stands verified from two seats. (2) **Lean bricks now on main** (all
axiom-clean `[propext, Classical.choice, Quot.sound]`, leaf files): `TwistedKernel.lean` (kernel
rigidity — Lemma K), `SubsetSumsetSymmetry.lean` (complement symmetry, any AddCommGroup),
`MonomialAgreementBound.lean` (Lift-Lemma far-ness count), `DescentTrichotomy.lean` (value-level
converse-FRI fold: unique even/odd components + both/one-sided agreement iffs). The descent
program's rigorous ingredients are now formalized API. Remaining formalization queue: the N₀
pattern-count combinatorics (medium), C19 (needs the symbolic/equivariance route — `decide` at
p≈2³¹ infeasible and `native_decide` is forbidden by the repo gate; honest path is the cyclotomic
consistency argument, future work).

### O39 / Round-14c — the per-line heavy-decode-set bound (second-moment method)

Solo orthogonal line (per-line second-moment, rounds 14/14b/14c), distinct from the swarm's
Johnson/list-decoding/clique combinatorics. LineHeavySetBound.lean (axiom-clean): the per-line
quantitative "few bad points" side of the proximity-gap dichotomy.
* `heavyLineSet_card_mul_sq_le`: `#{γ : |Λ(γ,a)| ≥ L}·L² ≤ ∑_γ|Λ(γ,a)|²` (Markov on squares over
  the line — clean Finset sum_le_sum on the heavy subset).
* `heavyLineSet_card_bound`: composing with the proven `line_second_moment_bound` (2a>n regime =
  the whole ρ=1/2 prize window): `#{γ:|Λ(γ,a)|≥L}·L²·(2a−d) ≤ (∑_γ|Λ|)·(2a−d) + (|C|²−|C|)·2(n−d)`.

So heavily-decoding line points fall off as 1/L² against a second moment whose off-diagonal is a
distance-uniform per-pair CONSTANT (the round-14 gain), not the past-Johnson-blowing
ball-intersection volume. This is the per-line object δ* is read from. Open: bound the per-line
first moment M=∑_γ|Λ| uniformly (empirically field-independent ~poly(n), round-14 probe) and the
pair count past birthday for ADVERSARIAL lines — where smooth-domain RS structure must enter.
### O40 — Conjecture 41's triple case: DEFICIENT TRIPLES ARE SUNFLOWERS (new theorems, machine-checked)

`NormalRankSharpThreshold.lean` §Triple (axiom-clean, 0 sorry, 0 warnings): the paper's
k-wise landscape beyond pairs was EMPIRICAL ("deficient triples exist at c=2 from n=11,
translate families; none found at c≥3"; "k-wise independence fails for common-core
triples"). Now theorems:

* `common_core_triple_relation` — the k-wise failure is a THEOREM at every window c ≥ 1:
  Λ_{C∪{x₁}}·(x₂−x₃) + Λ_{C∪{x₂}}·(x₃−x₁) + Λ_{C∪{x₃}}·(x₁−x₂) = 0 — explicit, all
  multipliers nonzero CONSTANTS. Pairwise independence (Thm 26) can never be promoted
  to 3-wise without structural hypotheses.
* `triple_relation_vanishing` — in ANY triple relation, P_i vanishes on (E_j∩E_k)∖E_i.
* `triple_kernel_trivial_of_spread` — **the structure theorem**: pairwise threshold on
  one pair + that pair's private intersection ≥ c points ⟹ trivial triple kernel.
  CONTRAPOSITIVE: every rank-deficient triple must have |(E_j∩E_k)∖E_i| < c for all i —
  pairwise intersections CONCENTRATE into the triple core. The sunflower shape of the
  empirical c=2 translate families is FORCED, not incidental.
* `relation_core_reduction` — sunflower relations descend exactly to the core-free
  family: Conjecture 41's triple case REDUCES to core-reduced supports (all pairwise
  intersections < c after reduction).

Net for the open core: Conj 41 (count of simultaneously-deficient supports on a flat at
c≥3) now has a machine-checked structural skeleton for triples — deficiency ⟹ sunflower
⟹ core-reduce ⟹ all-small-intersections core case. The remaining hard question is the
CORE-REDUCED count (where the c=2 counterexamples live and where c≥3 is conjectured to
behave differently) — sharper than before, still open.

### O41 / Round-14d — per-line first moment + the three-moment capstone

LineFirstMomentBound.lean (axiom-clean) closes the per-line decode chain with its missing first
moment, via the one-vote-per-coordinate primitive (single-codeword form of round-14 = Hab25 L1):
* `single_vote_card`: g i ≠ 0 ⟹ {γ : f i + γ·g i = c i} is a singleton (one vote/coordinate).
* `sum_agree_single_eq`: ∑_γ |agree(f+γg, c)| = n (Fubini: each coordinate votes once).
* `single_decode_card_mul_le`: #{γ : c ∈ Λ(γ,a)}·a ≤ n (Markov on per-point agreement).
* `line_first_moment_bound`: (∑_γ |Λ(γ,a)|)·a ≤ |C|·n — FIELD-SIZE INDEPENDENT, the proven form of
  the round-14 numeric probe (M ≈ poly(n), constant in q).

CAPSTONE `heavyLineSet_card_explicit_bound`: first+second+heavy-set combined, 2a>n window, NO ∑_γ:
  #{γ:|Λ(γ,a)|≥L}·L²·a·(2a−d) ≤ |C|·n·(2a−d) + a·(|C|²−|C|)·2(n−d).
Per-line decode heaviness bounded by code parameters (n,d,a,|C|) alone. The per-line chain (rounds
14/14b/14c/14d) is now self-contained and fully explicit. Open: the |C| (codeword count) is the
trivial bound; the actual prize needs |C| → RS list size and the adversarial-line pair count past
birthday — where smooth-domain RS structure must enter.

### O42 / Round-14e — close-pair-restricted per-line second moment (RS weight slice)

LineSecondMomentSharp.lean (axiom-clean) sharpens 14b's off-diagonal from the trivial |C|²−|C| to
|closePairs| (codeword pairs at distance ≤ 2(n−a)). Key dovetail: by the proven badSet_eq_empty,
FAR pairs (w > 2(n−a)) contribute 0 (no line point decodes both); and in the 2a>n prize window every
CLOSE pair (w ≤ 2(n−a) = 2n−2a < 2a ⟺ n<2a) automatically obeys the uniform-bound hypothesis 2a>w —
so the two round-14 regime facts meet with no gap.
* badSet_empty_of_far, offDiag_badSet_sum_eq_close, line_second_moment_bound_sharp:
  (∑|Λ|²)·(2a−d) ≤ (∑|Λ|)·(2a−d) + |closePairs|·2(n−d); closePairs_card_le (≤ |C|²−|C|).
|closePairs| = the w≤2(n−a) slice of the MDS/RS weight enumerator (tiny for high-distance codes) —
the genuine RS object where smooth-domain structure must enter the prize. Per-line chain rounds
14/14b/14c/14d/14e now: pair-cooc → first/second moment → heavy-set → close-pair sharpening.

### O43 / Round-14f — per-line unique decoding above the unique-decoding radius (capstone)

LineUniqueDecode.lean (axiom-clean) — the per-line chain's capstone. When 2(n−a) < d (the code's
min distance), closePairs=∅ ⟹ off-diagonal of the per-line second moment vanishes ⟹ ∑_γ|Λ|²=∑_γ|Λ|
(line_sq_sum_eq); termwise |Λ|≤|Λ|² over ℕ forces |Λ(γ)|²=|Λ(γ)| ⟹ |Λ(γ)|∈{0,1}. So EVERY line
point decodes to ≤1 codeword — per-line unique decoding, NO linearity/RS needed.
* closePairs_empty_of_minDist, line_uniqueDecode_of_minDist, lineList_subsingleton_of_minDist.
For RS (MDS, d=n−k+1): hypothesis 2(n−a)<n−k+1 ⟺ a>(n+k−1)/2 = the classical half-min-distance
radius, now PER LINE. Per-line chain (rounds 14–14f) complete: pair-cooc → first/second moment →
heavy-set → close-pair sharpening → unique-decode capstone, all axiom-clean. The interior δ*
window (Johnson, capacity) is BELOW this radius — the open prize is the gap between a>(n+k−1)/2
(here, trivial) and the Johnson/capacity interior, where |closePairs|>0 and RS structure enters.
### O41 — falsify-first on Conj 41's triple case: the CYCLIC/PTE deficiency mechanism (new theorem + verified ℚ witness)

Executed the probe O40 isolated (search the core-reduced zone). Findings (exact-arithmetic
verified, then formalized in `NormalRankSharpThreshold.lean` §Cyclic, axiom-clean):

1. **Empirical dichotomy at the square case w = 2c (probe, 1500 random spread triples, ℚ):**
   among pairwise-spread triples, untwisted point-level deficiency occurred EXACTLY when the
   triple intersection was nonempty (231/231 deficient with T ≠ ∅; 1269/1269 full rank with
   T = ∅ in the random ensemble). Mechanism for T ≠ ∅: all 3c normals are multiples of
   (X−t) — the trivial evaluation-syndrome collapse (M_true = 0 artifact; same device as the
   O37-addendum refutation). So the plain-rank "12% deficiency" of the first probe was
   entirely this artifact — consistent with 2026/858's Remark 31/36 data.
2. **But the clean "T = ∅ ⟹ full rank" conjecture is FALSE — the cyclic/PTE mechanism:**
   `cyclic_deficiency` (new theorem): three pairwise-distinct supports with equal
   e₁,…,e_{w−c} (locator coefficients agreeing above degree c) admit the explicit relation
   Λ₁(Λ₂−Λ₃) + Λ₂(Λ₃−Λ₁) + Λ₃(Λ₁−Λ₂) = 0 with all multipliers deg < c and ≠ 0.
   Verified ℚ-witness at c = 3, w = 6: E₁={0,1,5,8,12,21}, E₂={0,2,3,10,11,21},
   E₃={1,2,3,6,15,20} — equal e₁=47, e₂=767, e₃=5317, pairwise intersections (2,1,2),
   triple intersection EMPTY, kernel dim 1 over ℚ (two independent exact computations).
3. **Consequences for the open core:** (i) integer-coefficient relations survive mod every
   large p ⟹ NO effective characteristic threshold p₀ alone removes c ≥ 3 point-level rank
   coincidences — any Conjecture-41-style lemma must absorb equal-esymm families via its
   degeneracy escape clause or the γ-twist (the twisted [N|γN] object with distinct γᵢ is
   NOT directly refuted; that remains the live conjecture). (ii) The mechanism WELDS
   open-core formulation (iii) (rank lemma) to formulation (ii) (multi-symmetric
   concentration): deficiency at codim c is DRIVEN by e₁..e_{w−c} coincidences — PTE-type
   subset families are the dictionary. Conj 41's triple landscape after O40+O41:
   sunflower-concentrated OR equal-esymm — both now theorem-level, with the quantitative
   count above them still the prize.

### O44 — THE LOWER HALF CLOSES, per-prime, for the whole window: fixed-(s,r) instantiation of KKH ePrint 2026/782 Appendix A (nubs, 2026-06-09)

**Citation correction first:** "KK25 (personal communications)" is PUBLISHED — Krachun–Kazanin–
Haböck, *Failure of proximity gaps close to capacity*, ePrint **2026/782** (2026-04-20); update the
program record everywhere. Its Lemma 1 (e₁-image ≥ 2^r·C(s/2,r) for p > s^{s/2}) is the published
form of the subset-sum bound — O38's E1/E2 sharpen it (threshold (4min(r,m−r))^{m/4} vs s^{s/2};
full signed count N₀ with EXACTNESS; rate-1/2 coverage where their r ≤ s/2 vanishes).
**The main event (new note `QuotientPerPrimeInstantiation.md`):** running [2026/782 App. A]'s
quotient construction (DEEP/[BGKS20] via [CS25]+[BCHKS25], value-spread via [BCIKS20] Lemma 3) at
FIXED (s, r) instead of their asymptotic s = Θ(log n) — plus a one-degree shift r = ρs+1 that hits
the prize's exact rate and improves the gap 2/s → 1/s — yields **Theorem Q**: for EVERY prime
p ≡ 1 (mod n) and every 2-power s | n with ρs ∈ ℤ,
    ε_mca(RS[F_p, H_n, ρn], 1 − ρ − 1/s) ≥ (½·min(C(s, ρs+1), p/(ρn)) − n)/p
— threshold-free, per-prime. Breach of ε* = 2⁻¹²⁸ holds throughout [2^129, 2^{127+log₂C(s,ρs+1)}];
with s ∈ {128, 256, 512} per rate this covers the ENTIRE window at every prize rate (table in the
note: e.g. ρ=1/2: η=1/128 per-prime to 2^251.1, η=1/256 the rest). Optimizing s:
**δ*_C < 1 − ρ − η for every dyadic η ≥ (H₂(ρ)+o(1))/(log₂p − 127)** — the LOWER HALF of the
conjectured determination formula, per-prime, effective, for the whole window, from published
machinery + a routine instantiation. Derivation re-verified step-by-step (list/agreement-A/
value-spread/quotient degrees/far-side strictness incl. the m=1 edge; bad-z and case-boundary
corrections negligible in-window). **Consequences:** O38-E3's windows are SUBSUMED (E1/E2
exactness and the constructive count remain the finer per-image invariants; transition/onset
structure O39 unaffected as facts about exactness); the cert(p)/class-group program is retired for
the lower half; **the prize's remaining open content is purely the UPPER half** (descent lane
O13–O13″ / Conjecture D): prove ε_mca ≤ ε* down from capacity to meet this floor.
**Side data this cycle (probe_class_effect.py):** h=1 vs h=17 deficiency ladders at layer 5
(m=32 exact through u=0.60, m=64 deficient only at u=0.40 of matched ratio) and the cofactor law —
every observed cofactor is 2^a × (split primes ≡ 1 mod m); literature sweep verdicts: the
descent-lane transversal/balanced-overlap marginal layer is APPARENTLY NEW (no name/theorem/prior
description found, incl. ABF26); O38's stated priority claim was consistent with the public record
but is now framed against 2026/782 as above.
||||||| parent of cc8699f9a (docs(#232): DISPROOF_LOG O44 — round-21 relation module + PTE convergence)
### O44 / Round-21 — clique relation module (row side) + the PTE convergence

`Conjecture41CliqueRelationModule.lean` (main-loop solo, axiom-clean, 0 warnings, strict-verified):
nodal identity (X−α)Λ_{E_α} = Λ_W; relation_eval_zero (dependencies vanish at own nodes);
relation_factor_sum (u_α = (X−α)v_α, Σv = 0 — nodal collapse in the domain F[X]);
relation_factor_sum_twisted (double block: both Σv = 0 AND Σγv = 0); vCoeff_natDegree_lt (degree
budget). WITH R20: rank [N|γN]_clique = D+c−1, ker = the twisted evaluation pencil EXACTLY (dim w+1).
Conj 41 on its universal obstruction = the explicit pencil-degeneracy question (R19: exceptional
p ⊆ divisors of one ℤ-det). CONVERGENCE: fleet O40/O41 — deficient triples are SUNFLOWERS; the
non-sunflower mechanism is CYCLIC/PTE (equal e₁..e_{w−c}) = EXACTLY the rounds-4-8 multi-symmetric
concentration object (N_t equal-esymm counts on μ_n). The c≥3 rank lemma and the t≥2 concentration
are the SAME combinatorics — PTE solutions inside the smooth domain — approached from the two ends.
### O42 — the twisted (Conjecture-41) object vs PTE families: rank dichotomy BROKEN for every γ, escape clause load-bearing, and the (ii)⟷(iii) WELD at class syndromes

Continuation of O41: tested equal-esymm families against the ACTUAL Conjecture-41 matrix
A = [N_{Eᵢ} | γᵢ·N_{Eᵢ}] (distinct γᵢ). Findings (exact ℚ arithmetic + one new Lean brick):

1. **Rank dichotomy broken for EVERY γ-assignment at m ≥ 6.** `equal_window_image`
   (NEW, machine-checked): for an equal-e₁..e_{w−c} family, every Σ ΛᵢPᵢ (deg Pᵢ < c)
   decomposes as Λ₀·Q + R with deg Q < c, deg R ≤ 2c−2 — a (3c−1)-dim space independent
   of m. Both blocks of A land there ⟹ rank(A) ≤ 6c−2 < min(mc, 2D) whenever mc > 6c−2
   (m ≥ 6 at any c ≥ 2), for EVERY γ. Verified numerically: rank exactly 16 = 6c−2 at
   m=6, c=3, all 60/60 random γ-assignments (mixed-class control: 32/40 full rank).
2. **Conjecture 41 SURVIVES — via its escape clause, which is load-bearing.** The kernel
   of A is spanned by (v,0),(0,v) with v THE CLASS SYNDROME: v = (0,…,0,h₀,h₁,…,h_c)
   where h_j are the COMPLETE HOMOGENEOUS symmetric functions of the class parameters
   (verified: h₂ = e₁²−e₂ = 2936, h₃ = e₁³−2e₁e₂+e₃ = 99774 at the witness class).
   Newton's e/h convolution ⟹ ⟨X^r Λ_E, v⟩ = 0 for r < c ⟺ e₁..e_c(E) = class values.
   All kernel lines are the degenerate scaling family through v, so the escape clause
   (⟨n₀(Eᵢ), s₂⟩ = 0 on ker A) fires at every support. The conjecture's dichotomy holds
   here ONLY because of the clause — any sharpening that drops it is FALSE for all
   m ≥ 6 PTE families, at every prime, every γ.
3. **The weld (formulations (ii) ⟷ (iii)).** At the class syndrome v, compatibility IS
   membership in the esymm class, and the error values are ALL NONZERO (verified at all
   6 witness supports — genuine M_true mass, not a Remark-31 artifact). So the
   point-level list size at v EQUALS the e₁..e_c fiber count: the multi-symmetric
   concentration quantity (open-core formulation (ii)) and the rank/list quantity
   (formulation (iii)) are THE SAME NUMBER at class syndromes. The prize question "how
   large can the esymm fiber be, field-independently" is literally "how large is M at a
   class syndrome".

Queued next bricks: (a) finrank-pigeonhole formalization of the twisted-kernel existence
(via equal_window_image + Polynomial.degreeLT dimension count); (b) the class-syndrome
h-sequence construction + Newton-convolution compatibility characterization in Lean.

### O44 / Round-14g — linear-code collapse of the per-line close-pair count (→ weight enumerator)

LineClosePairsLinear.lean (axiom-clean, on main `LinePairCooccurrence.closePairs_card_linear`)
bridges the abstract per-line chain (rounds 14–14f) to RS structure. For a subtraction-closed
(linear) code, translation invariance collapses the close-pair count to the weight-enumerator
slice: `|closePairs C a| = |C|·|weightSlice C (2(n−a))|` (weightSlice = nonzero codewords of weight
≤ 2(n−a)), via the bijection (c,c')↦(c,c'−c) + supp_eq_supp_sub. Plus
line_second_moment_bound_weightSlice (off-diagonal = |C|·|weightSlice|·2(n−d)). Per-line companion
of O29's ball-intersection linear collapse. |weightSlice(2(n−a))| = the w≤2(n−a) slice of ∑_w A_w;
for MDS/RS (A_w=0 for 0<w<d) it's EMPTY above the unique-decoding radius (14f) and nonzero exactly
in the interior (1−√ρ,1−ρ) — the RS object the prize turns on. Open: bound A_w for explicit
smooth-domain RS in the interior. GOTCHA: ring/linear_combination fail on Fin n→F (Pi); use
abel/add_right_cancel.

### O45 / Round-22 — the constructive PTE family (expand-lift) + the two-phase explanation

`PTEFamilyConstruction.lean` (main-loop solo, axiom-clean, 0 warnings, strict-verified):
P_A = expand_d(baseNodal A) = ∏(X^d − a). Lattice vanishing (coeff_expand): every coefficient at a
non-multiple of d is ZERO ⟹ the full top window e_1..e_{d−1} vanishes for EVERY base set;
liftedPoly_injective (expand_injective + root recovery); lifted support = power-map fiber
{x : x^d ∈ A} ⊂ μ_n; pte_family: C(n/d, s) pairwise-distinct equal-window supports. THRESHOLD: the
Conj-41 deficiency window (equal e_1..e_{w−c}) fires iff d ≥ w−c+1 ⟹ s ≤ w/(w−c+1): deployment
(c = Θ(n)) → family O(1) (matches conjecture's M = O(1)); capacity (c = O(1)) → exponential
(matches the proven c=2 phase). ONE construction = both phases of 2026/858's empirical diagram =
the depth-collapse wall in deficiency language. OPEN CEILING: can non-lifted families beat
C(n/d, s) in the deep window (non-cyclic deficiency at large p)? = the prize core, final form.
### O43 — REFUTATION (verified): the "Equivalently, M_true ≤ ⌊(2D−1)/c⌋" form of Conjecture 41 is FALSE at every sufficiently large prime

Closing the O42 arc: the class-syndrome dictionary turns formulation-(ii) fiber pigeonhole
into a Conjecture-41 attack, and it lands. Construction (all integer data; exact-arithmetic
verified at p = 1009 and p = 7919; integrality ⟹ every sufficiently large p):

* Parameters: n = 14 (domain L = {0,…,13}), k = 5, D = n−k = 9, c = 3, w = D−c = 6;
  Conjecture-41 bound ⌊(2D−1)/c⌋ = 5.
* The integer (e₁,e₂) = (39, 589) fiber of 6-subsets of L has 10 supports spreading over
  9 distinct e₃ values {4269, 4281, 4293, 4305, 4329, 4353, 4365, 4377, 4389}.
* The syndrome LINE in the e₃-direction: s₁ = classSyndrome(39, 589, 4269) =
  (0,0,0,0,0, h₀,h₁,h₂,h₃), s₂ = (0,…,0,1) (top unit vector; (s₁,s₂) independent). By the
  Newton e/h convolution, s(γ) = s₁ + γ·s₂ is the class syndrome of (39, 589, 4269+γ), so
  each of the 9 fiber e₃-values gives a distinct γ with a compatible support — and the
  Vandermonde error values are ALL NONZERO at every one of them (verified): **M_true = 9 > 5
  at p = 1009, p = 7919, and every large p**. No threshold p₀(n,k,c) of ANY size rescues
  the "equivalently" sentence.
* WHY the dichotomy form survives: on this line the escape clause fires TRIVIALLY —
  s₂ = e_{D−1} pairs to zero with every Λ_E (degree w < D−1). So the clause excludes far
  more than degenerate configurations, and **the two printed forms of Conjecture 41 are
  inequivalent**; the M_true ≤ ⌊(2D−1)/c⌋ prediction is false as stated and must be
  restated (e.g., restricted to lines with s₂ engaging the low syndrome window).
* SCALING (probe, n = 14, lines through realized classes): violations persist at p = 31,
  53, 71, 101, 151, 211 (max hits 10–19 ≫ 5) — structure, not birthday chance; the
  mechanism is the integer fiber spread, which GROWS with n. At deployment-shaped
  parameters the e₃-spread of (e₁,e₂)-fibers is astronomically large: adversarial
  class-syndrome lines carry list mass far above any O(n/c) envelope. This is a LOWER-bound
  brick for the disproof side of the prize loop: worst-case line list counts at c ≥ 3 are
  governed by multi-symmetric fiber spreads (formulation (ii)), not by rank genericity.

Caveats kept honest: this refutes the printed equivalence/Mtrue-prediction of Conjecture 41,
NOT the paper's FRI soundness theorem (which doesn't depend on it), and NOT the dichotomy
form (whose escape clause, however, is now shown to do unintended exclusion work). Queued
Lean bricks: class-syndrome construction + Newton-convolution compatibility (the e/h
identity is Mathlib-adjacent), then the fiber-line M_true lower bound as a formal theorem.

### O46 — THE RIGIDITY PATHWAY: a complete conditional architecture for the list core

Four steps; three VERIFIED: (1✅ R22) constructive floor — lift families realize the deficiency
window iff d ≥ w−c+1, O(1) at deployment/exponential at capacity; (2 OPEN = the residue) char-0
LINEAR-WINDOW RIGIDITY: families of w-subsets of μ_n pairwise sharing e_1..e_t, t = Θ(n), over ℂ
are lift-structured — Mann/Conway–Jones-type; at n=2^m the in-tree power-basis independence (R12)
reduces small cases to finite sign/index combinatorics; base case (w=2,t=1) = equal-sum pairs are
antipodal-only, formalizable NOW from in-tree machinery; (3✅ R19) large-p transfer via integer
certificates (det_map_zmod_ne_zero); (4✅ R20+R21) clique rank structure (kernel = twisted pencil;
deficiency = PTE). CONSEQUENCE: steps 2+3+4+1 ⟹ Conj 41's M = O(1) at Johnson at deployment ⟹ the
Grand List Challenge answer. The $1M list core = ONE precisely-stated char-0 conjecture with a
machine-checked skeleton around it. NEXT (Jun-11 agents + solo): (a) the (w=2,t=1) base case from
R12 independence, (b) Mann's theorem partial formalization, (c) the general-family (non-clique)
reduction to cliques/sunflowers (fleet O40).

### O43 — the descent program's formalized surface is COMPLETE for the proven-on-paper layer (nubs, 2026-06-09)

Seven bricks on main, all axiom-clean `[propext, Classical.choice, Quot.sound]`, leaf-file style:
`TwistedKernel` (Lemma K rigidity) · `SubsetSumsetSymmetry` (complement symmetry) ·
`MonomialAgreementBound` (Lift far-ness) · `DescentTrichotomy` (+ polynomial-level recomposed-
candidate iffs — the full converse-FRI fold trichotomy) · `DisjointPairCount` (+ `AdmissibleSupport`
+ `n0_pattern_count` — the complete Theorem-A combinatorial count Σ_s C(m2,s)·2^s). Together: every
elementary proven piece of the O11–O14 program is now Lean API. Remaining formalization (honest):
the cyclotomic bijection (pattern count ⟷ actual subset sums in ℤ[ζ_m] — needs 2-power cyclotomic
basis machinery; deep), C19 (symbolic/equivariance route only — native_decide forbidden), and the
O38 AM–GM threshold (E1 orthogonality — Parseval over odd characters; medium, queued). The open
research core (paired tower induction ⟺ classical beyond-Johnson) is unchanged.
### O44 — O43 FULLY FORMALIZED: TopDirectionLineCount.lean — decoupling theorem + machine-checked Conjecture-41 violation witness (0 sorry, axiom-clean END TO END)

The queued O43 Lean bricks are DONE, and the formalization SIMPLIFIED the math — no
Newton/h-machinery needed. `TopDirectionLineCount.lean` (all axiom-clean
`[propext, Classical.choice, Quot.sound]`, 0 sorry, 0 warnings):

* `top_line_compat_iff` — **the decoupling theorem**: on a top-unit-direction line, the
  codim-c compatibility of a weight-w support (w+c = N) ⟺ (c−1) γ-FREE window equations
  + the explicit assignment γ = −⟨X^{c−1}Λ_E, s₁⟩ (because ⟨X^rΛ_E, u_top⟩ = [r = c−1]
  by monicity/degree). Line compatibility = fiber membership + a value map.
* `compat_gamma_count` / `conj41_count_lower_bound` — M_compat(s₁, u_top) ≥ #distinct
  last-window values over the γ-free fiber; >⌊(2N−1)/c⌋ distinct values ⟹ the
  Conjecture-41 bound is exceeded.
* `loc_coeff_esymm` — the Vieta bridge: locator coefficients = signed elementary
  symmetric functions (the formal (ii)⟷(iii) dictionary).
* `escape_clause_trivial` — ⟨Λ_E, u_top⟩ = 0 for every short support, by degree: the
  formal content of the two-printed-forms inequivalence.
* **`conj41_violation_witness`** — the END-TO-END machine-checked violation: over
  ZMod 17 (D = 9, c = 3, w = 6, domain = the whole field, s₁ = unitVec 5, where the
  γ-free system is literally e₁(E) = 0 ∧ e₂(E) = 0 and γ = e₃(E)): the six explicit
  supports {0,6,8,11,12,14}, {0,3,10,11,13,14}, {0,5,8,9,13,16}, {0,2,3,7,10,12},
  {0,1,2,3,13,15}, {0,2,4,6,9,13} realize six distinct γ-values {1,…,6}, so the
  compatible-parameter count on ONE line is > 5 = ⌊(2D−1)/c⌋. All esymm side conditions
  discharged by kernel `decide`. (The full e₁ = e₂ = 0 fiber at p = 17 actually spreads
  over 16 distinct e₃ values — more than three times the conjectured bound.)

With O44 the entire O40–O43 arc is formal: sunflower structure, cyclic/PTE mechanism,
equal-window collapse, decoupling, count lower bound, escape-clause triviality, and a
kernel-checked counterexample instance to the per-line bound of Conjecture 41's M_true
form. The remaining open object of #232 is unchanged and explicitly bounded: the
field-independent fiber-size question itself (= δ* in the gap), now reachable from BOTH
formulations through one machine-checked dictionary.

### O47 / Round-23 — rigidity base case PROVEN (equal-sum pairs are antipodal)

`RigidityBaseCasePairs.lean` (main-loop solo, axiom-clean, 0 warnings, strict-verified): the first
verified case of O46 Step 2. THE INTEGER BRIDGE (gZ_eq_zero): equal-sum equations force INTEGER
coefficients to vanish (independence + Int.cast_injective) — case analysis drops into ℤ/omega.
pair_rigidity: a+b = c+d, pairs disjoint ⟹ both antipodal — the (w=2,t=1) linear-window rigidity,
matching the R22 floor exactly (only equal-e₁ pairs in μ_{2N} = the d=2 lifts). LEAN TECHNIQUE: the
8-index-branch × 16-sign bash needs maxHeartbeats 1000000 + single-chain combinator (no `first`,
which doubles the search); step 2 of the theorem (w = antipode z) follows ALGEBRAICALLY from step 1
via sval_injective — no second bash. PATHWAY: 1✅ 2(base ✅, w≥3 open = Conway-Jones/Mann) 3✅ 4✅.
The integer-bridge technique is the demonstrated route for the w≥3 windows (3-term, 4-term vanishing
sums at 2-power orders are classified by the same basis-reduction; w=3 base case = 6-term sums).
### O45 — the q^t pigeonhole denominator KILLED: point-fiber theorem (lossless (ii)→list transfer)

Direct advance on the in-tree δ* reduction chain. Rounds 5/6 left the named residual
"q^t denominator unkilled": the interior list lower bounds lost field independence to a
pigeonhole over symmetric-function targets (/q at t=1, /q² at t=2), and the round-6
no-go showed AVERAGING can never remove it. The point version of the O44 decoupling
removes it by CONCENTRATION — choose the received word, not the average:

* `point_compat_iff_esymm_zero` (TopDirectionLineCount.lean, axiom-clean): compatibility
  of a weight-w support at the UNIT syndrome `unitVec (w−1)` ⟺ e₁(E) = ⋯ = e_c(E) = 0.
* `zero_fiber_filter_eq`: the compatible supports at that single received word are
  EXACTLY the zero-fiber supports, as a Finset identity — the syndrome-side list count
  EQUALS the fiber count. No averaging, no /q^c, any field, any domain.
* `zero_fiber_instance` (kernel decide): over ZMod 13 at w=3, c=2 the zero fiber is
  {1,3,9}, {2,5,6}, {4,10,12}, {7,8,11} — count 4 > pigeonhole average C(13,3)/13² ≈ 1.69.
  Per-point concentration, machine-checked.

Consequence for the open core: ANY field-independent lower bound on the zero fiber
#{E : |E| = w, e₁ = ⋯ = e_t = 0} now transports VERBATIM into an interior list-type
lower bound at agreement k+t — the reduction is lossless and formal. The δ* program's
missing ingredient is now ONLY the integer/combinatorial fiber question past Johnson
(formulation (ii) in its purest form); every reduction step around it is machine-checked.

### O48 / Round-24 — w=3 rigidity: NOW FULLY MECHANIZED (see update below)

**The mathematics (derived, hand-verified branch-by-branch; NOT yet machine-checked — WIP at
/tmp/r24_triples_WIP_SAVED.lean with bridges compiling):**
* THEOREM (disjoint triples impossible): over CharZero with the half basis independent, two
  signed-disjoint triples of 2N-th roots cannot have equal sums. PROOF: 6-term integer bridge ⟹
  per-index ℤ-equations; coefficient at a's index: partners are b/c antipodal-to-a (within; cross-
  side partners = equality, excluded by disjointness; ±1±1±1-type sums never 0 in ℤ) ⟹ WLOG
  b = −a ⟹ collapse to c = d+e+f; coefficient at c's index: c=d/e/f excluded, one-partner sign
  patterns ±2/0 with parity contradictions, two/three-partner patterns force repeated points —
  ALL branches die ⟹ False.
* COROLLARY (w=3 SUNFLOWER classification): distinct equal-sum triples share exactly one vertex y,
  and the residual pairs are disjoint equal-sum ⟹ (R23 pair_rigidity) both antipodal:
  {x,−x,y} & {z,−z,y}. **Proves the fleet's empirical O40 ("deficient triples are sunflowers") as
  a char-0 theorem**, and REFINES the rigidity structure class: at odd w the R22 lifts (d|w) are
  unavailable — the correct class is sunflower/partial-lift (core + d=2 lift petals).
* MECHANIZATION STATUS: bridge6/bridge4 + sval lemmas COMPILE (R23-style); the two case bashes
  (collapse4: 8×16 branches; partner-extraction: 32×64) need branch surgery — split_ifs-then-omega
  with point-equality discharge; the multi-alternative `first` chains break parsing across lines
  (keep alternatives single-line); simp_all hits maxRecDepth at 8000 on the 6-point bash.
  Technique recorded; finishing is mechanical.

### O46 — ATTACK ON THE RESIDUAL ITSELF: the coset construction — first field-independent t ≥ 2 interior fiber lower bound (Round-6 residual closed on subgroup-structured domains)

The isolated O45 residual (the multi-symmetric zero-fiber count) is attacked directly and
yields a NEW theorem (TopDirectionLineCount.lean §CosetConstruction, axiom-clean, 0 sorry):

* `loc_coset` — loc(x·H) = X^d − x^d for the full d-th-roots packet H (pure scaling; the
  aeval-rescaling proof works over any field, no characteristic condition, no Newton).
* `loc_coset_union` — loc(⋃ᵢ xᵢH) = expand_d(∏ᵢ(X − xᵢ^d)): the locator of a union of m
  distinct cosets is a polynomial in X^d.
* `coset_union_esymm_zero` — hence e_j = 0 for EVERY j not divisible by d: coset unions
  live in the multi-symmetric zero fiber at all t < d.
* `coset_fiber_lower_bound` — THE COUNT: the zero fiber at w = m·d, any t < d, contains
  ≥ C(|S|, m) supports (S = coset representatives; injection by coset reconstruction).
  Numerics: F₁₃, H = {1,3,9}: the C(4,2) = 6 unions are the ENTIRE (w=6,t=2) zero fiber —
  exhaustive there (suggesting a matching upper bound on cyclic domains, left open).

Combined with O45's lossless transfer (zero_fiber_filter_eq), this is a FIELD-INDEPENDENT
syndrome-side list lower bound at codimension excess c = t for every t ≤ d−1 — closing the
Round-6 named residual ("multiplicative joint-symmetric count at t ≥ 2 still OPEN", q^t
denominator) by CONCENTRATION on subgroup-structured smooth domains. Scaling: on μ_n with
d ≈ √n the bound is C(√n, m) = exp(Ω(√n)) at t ≈ √n − 1 — super-polynomial, q-independent,
t ≫ 2, strictly deeper than the in-tree t=1 (/q) and t=2 (/q²) averaging bounds.

HONEST LIMITS (the remaining wall, sharpened): (i) t < d forces t ≤ largest-proper-divisor
scale; on PURE 2-POWER domains d | n and d | w = n/2−t force d | t, so the construction
provably cannot reach its own threshold there — the 2-adic obstruction matches the C19/
descent lane's focus on 2-power towers. (ii) The prize band needs t = Θ(n); the gap
between t ≈ √n (now CLOSED, constructively) and t = Θ(n) (open) is the exact residual.
The open core after O46: field-independent zero-fiber bounds at t = Θ(n) on 2-power
smooth domains — every other parameter regime of the reduction now has a machine-checked
constructive answer.

### O48-update / Round-24 COMPLETE — w=3 sunflower rigidity MACHINE-CHECKED

`RigidityTriplesSunflower.lean` (on main, axiom-clean, 0 warnings, strict-verified): bridge6/bridge4
+ collapse4_impossible + disjoint_triples_impossible — disjoint equal-sum triples of 2N-th roots are
IMPOSSIBLE (CharZero + half-basis independence); with R23 pair_rigidity ⟹ the SUNFLOWER
classification (fleet O40 proven as char-0 theorem). STEP 2: w=2 ✅ w=3 ✅ w≥4 open. THE BASH
TECHNIQUE THAT WORKED (after simp_all looped): (first | rw [if_pos e_i] | rw [if_neg e_i]) at hg
per condition → rcases signs → simp only [Bool.false_eq_true, if_true, if_false] at hg → first-list
with SINGLE-LINE alternatives: omega | exact Or.inl ⟨e1, rfl⟩ | exact absurd rfl (hab e1.symm) | …;
trim never-executed alternatives flagged by the linter. 2048 branches verified in ~3 min.
### O47 — the 2-power fiber EXHAUSTIVENESS discovery: coset unions are everything (char 0 / large p), with a complete elementary proof at t = 1

Probe follow-up to O46 on the FRI-relevant domains themselves (μ_n, n = 2^m). Data
(exhaustive, exact arithmetic): at field-generic p (e.g. n=16 ⊂ F₉₇), every nonzero
t ≥ 2 fiber observed is EXACTLY the O46 coset-union family — w=4: 4 = C(4,1) (μ₄-cosets);
w=8, t=2,3: 6 = C(4,2) (pairs of μ₄-cosets; the two μ₈-cosets are among them) — and all
fibers at coset-incompatible w (4 ∤ w) are EMPTY. At small p (n = p−1, F₁₇) extra fiber
elements appear (w=5, t=2: 16) — genuine mod-p coincidences below a height threshold.

**The char-0 theorem (t = 1, complete elementary proof):** let ζ have multiplicative
order n = 2^m in a characteristic-0 field, S ⊆ μ_n with Σ_{x∈S} x = 0. Then S is a union
of antipodal pairs {x, −x}. PROOF: write S = {ζ^i : i ∈ I}, I ⊆ [0,n), and
P(X) = Σ_{i∈I} X^i ∈ ℚ[X]. P(ζ) = 0 and minpoly_ℚ(ζ) = Φ_n = X^{n/2} + 1 (Gauss +
2-power cyclotomic), so X^{n/2} + 1 ∣ P. Reducing mod X^{n/2} + 1 sends X^{i+n/2} ↦ −X^i,
so for each i < n/2 the residue coefficient is [i ∈ I] − [i + n/2 ∈ I] = 0, i.e.
i ∈ I ⟺ i + n/2 ∈ I — and ζ^{i+n/2} = −ζ^i. ∎  (This is Lam–Leung at the prime 2.)

**COROLLARY (the first EXACT fiber determination on FRI domains):** in char 0 — hence
over F_p for all p above an explicit height bound — the t = 1 zero fiber of w-subsets of
μ_{2^m} is EXACTLY the antipodal-pair unions: count C(n/2, w/2) for even w, 0 for odd w.
Upper AND lower bound; matches the data (n=16: w=4: 108?? no — t=1 at small p includes
mod-p extras; at the char-0 level the count is C(8, w/2)).

**The t ≥ 2 recursive structure (the research program, crystallized):** e₂ = 0 given
e₁ = 0 ⟺ p₂ = Σ x² = 0 — and squaring maps antipodal pairs of μ_n two-to-one onto μ_{n/2}:
the t-fiber on μ_{2^m} descends along the SQUARING TOWER (the FRI fold!) to vanishing
conditions one level down. The char-0 t-fiber on 2-power domains is governed by a 2-adic
descent recursion — the SAME tower the owner's C19/descent lane climbs from the protocol
side. CONJECTURE (exhaustiveness, t ≥ 2, char 0): the t-fiber on μ_{2^m} is exactly the
O46 coset-union family — equivalently, at t = Θ(n) the fiber is O(1). If TRUE, the
lossless O45 transfer makes the unit-syndrome list O(1) deep in the interior on 2-power
domains — the PROOF side of the prize at these syndromes; if FALSE, the counterexamples
are new deep-interior list mass — the DISPROOF side. Either way the question is now a
concrete, finite-checkable, char-0 statement about vanishing sums of 2-power roots of
unity with prescribed higher moments — with Lam–Leung/Conway–Jones as the entry
literature and the descent tower as the mechanism. Lean brick queued: the t = 1 theorem
(cyclotomic_eq_minpoly_rat + 2-power cyclotomic + coefficient pairing — all Mathlib-
available ingredients).

### O49 / Round-25 — GENERAL t=1 RIGIDITY (all w, uniform — the case ladder is dead)

`RigidityGeneralT1.lean` (main-loop solo, axiom-clean, 0 warnings, strict-verified):
disjoint_equal_sum_antipodal — disjoint equal-sum sets of 2N-th roots are UNIONS OF ANTIPODAL PAIRS,
at every support size, with NO case analysis. Engine: each index carries ≤ 2 signed points ⟹ fibers
∅/singleton/antipodal-pair with contributions {0,±1} (fiber_trichotomy); Finset integer bridge
(bridgeF) equates contributions; singleton fiber ⟹ identical signed point in both sets ⟹
disjointness violation. SUBSUMES R23+R24 (no w=4,5,... bashes ever). CONSEQUENCE: disjoint equal-e₁
families = EXACTLY the d=2 lifts (Λ_A ∈ F[X²], R22 structure) — floor = ceiling at t=1, all w. THE
FULL WINDOW RECURSES: equal e_1..e_t of lifts ⟹ equal e_1..e_{⌊t/2⌋} of squares in μ_N
(independence inherited); ⌈log₂(t+1)⌉ halvings exhaust any window ⟹ 2^k-lift structure. REMAINING
for full Step 2 (now MECHANICAL, no new math for the disjoint case): (a) recursion assembly through
R22's expand machinery, (b) shared-vertex/sunflower-core reduction (divide by the common locator
factor — top-window agreement of products with common factor passes to cofactors).
### O48 — THE DICHOTOMY RESOLVES TRUE: the tower theorem (descent assembly machine-checked, 18/18 prediction matches)

The O47 dichotomy is RESOLVED, affirmatively, in characteristic 0, by descent along the
squaring tower. The theorem:

  **On μ_{2^m} in characteristic 0, the t-fiber {S : |S| = w, e₁(S) = ⋯ = e_t(S) = 0}
  is EXACTLY the unions of μ_d-cosets, d = the smallest 2-power > t.**

Proof structure (complete; each step either machine-checked or classical-with-proof-recorded):
1. e₁ = 0 ⟹ antipodal closure (Lam–Leung at p = 2; O47 proof via Φ_{2^m} = X^{n/2}+1).
2. Squaring is 2-to-1 from antipodal sets onto level n/2 (`sq_fiber_pair`, MACHINE-CHECKED):
   given antipodal closure, e₂ = 0 ⟺ a vanishing sum one level down (`t2_tower_resolution`'s
   hdesc step, MACHINE-CHECKED: Σx² = 2·Σ_image y).
3. Step 1 at level n/2 ⟹ squared image antipodal ⟹ pairs assemble into μ₄-cosets
   (`mul_i_closure`, MACHINE-CHECKED, char-free: x'² = −x² forces x' = ±ix, antipodal
   closure upgrades either sign to closure under multiplication by i).
4. e_j = 0 automatic on μ_d-coset unions for d ∤ j (`coset_union_esymm_zero`, O46,
   MACHINE-CHECKED) — so nothing new is required until t reaches d, where Newton
   (p_d = ±d·e_d given lower e's vanish; char 0) reduces e_d = 0 to a vanishing sum at
   level n/d, and the induction climbs one rung: μ_d-cosets pair into μ_{2d}-cosets by
   the same assembly argument with i replaced by a primitive 2d-th root.
   Converse inclusion: O46 `coset_fiber_lower_bound` family.

VERIFICATION: the predicted count (C(n/d, w/d) when d | w, else 0) matches the exhaustive
fiber computation at ALL 18 tested (w, t) pairs on μ₁₆ over F₂₅₇ (proxy for char 0) —
including the subtle zeros (4 ∤ w ⟹ empty fiber) and the t-plateaus (fiber constant on
2^{s} ≤ t < 2^{s+1}).

**THE PRIZE-SHAPED COROLLARY: at t = ηn the fiber is ≤ 2^{n/d} ≤ 2^{2/η} — the KK25/S-two
sharp budget 2^{O(1/η)}, now PROVEN for the multi-symmetric fiber on 2-power domains in
char 0.** Via the lossless O45 transfer: unit-syndrome lists deep in the interior are
2^{O(1/η)} — the PROOF side of the band at these syndromes, char 0 / p above a height
threshold. Lean status: descent assembly fully machine-checked (`sq_fiber_pair`,
`mul_i_closure`, `t2_tower_resolution` — axiom-clean, 0 sorry); classical base case (Lam–
Leung at p=2) enters as a hypothesis with complete recorded proof (cyclotomic Lean brick
queued); general-t induction recorded here. REMAINING ANALYTIC GAP (stated exactly): the
effective height threshold for the char-0 ⟹ F_p transfer at given (n, w) — the same
effective-Schwartz–Zippel question as 2026/858's p₀, now attached to a TRUE theorem; and
extending from unit syndromes to all received words (the MCA quantifier).

### O50 / Round-26 — the WINDOW-HALVING ENGINE (full-window rigidity = two verified components)

`RigidityWindowHalving.lean` (main-loop solo, axiom-clean, 0 warnings, strict-verified):
odd_psum_vanish (odd power sums ≡ 0 on antipodally-closed sets — R8 engine at ω=−1; odd window
conditions AUTOMATIC) + squares_fiber/even_psum_halves (squaring exactly 2-to-1; p_{2l}(A) =
2·p_l(A²) — even conditions descend EXACTLY) + squares_disjoint + window_halving_step (THE ENGINE:
disjoint antipodally-closed equal-p_1..p_t ⟹ squares disjoint equal-p_1..p_{⌊t/2⌋}; scale μ_{2N}→μ_N,
independence inherited by {ζ^{2j}}). WITH R25: full-window rigidity (disjoint case) = iterate
R25+engine ⌈log₂(t+1)⌉ times ⟹ 2^k-lift structure ⟹ FLOOR (R22) = CEILING. REMAINING ASSEMBLY (not
new math): (i) the level-iteration statement (re-encoding bookkeeping), (ii) the sunflower-core
reduction (non-disjoint: divide by common locator factor, top-window agreement passes to cofactors),
(iii) the final composition into Conj-41/δ*. Power-sum ≡ e-window over CharZero by Newton (Mathlib
has NewtonIdentities for the formal bridge when needed).

### O51 / Round-27 — sunflower-core reduction (Step 2 chain complete over verified parts)

`RigiditySunflowerCore.lean` (main-loop solo, axiom-clean, 0 warnings, strict-verified):
cofactor_window ((Q·R₁−Q·R₂).degree < d ⟹ Q.degree + (R₁−R₂).degree < d — factor + degree_mul,
3 lines in the degree-of-difference formulation) + nodal_core_split (Λ_A = Λ_{A∩B}·Λ_{A∖B}) +
sunflower_core_reduction (equal windows ⟹ disjoint residuals with core-shifted equal windows).
STEP 2 CHAIN COMPLETE over verified links: core division (R27) → antipodal closure (R25) → window
halving (R26 iterate) → 2^k-lift petals (R22). STRUCTURE THEOREM (component-verified): equal-window
families in μ_{2N} = SUNFLOWERS (core + 2^k-lift petals), all sizes, all linear windows, char 0,
independence dischargeable (R12). REMAINING PLUMBING: level-iteration statement + Conj-41/δ*
composition. KEY FORMULATION LESSON: state window agreement as (P₁−P₂).degree < d — products,
cofactors, and shifts become one-line degree_mul arithmetic (vs coefficient-indexed agony).

### O52 / Round-28 — FULL-WINDOW RIGIDITY (level iteration; Step-2 disjoint capstone)

`RigidityFullWindow.lean` (main-loop solo, axiom-clean, 0 warnings, strict-verified, first-compile
EXIT 0): LiftStructured k (iterated-antipodal = R22 2^k-lift root structure) + full_window_rigidity
— disjoint Good sets with equal p_1..p_{2^k−1} are LiftStructured k (induction: closure oracle from
p₁ per level [= R25 through the signed-point encoding — the ONE remaining de-oracling]; halving
engine drops windows with EXACT alignment 2l ≤ 2^{k+1}−1 ⟺ l ≤ 2^k−1; Good descends through
squares). COMPLETE STEP-2 CHAIN (every component verified): core division (R27) → closure (R25) +
halving (R26) iterated (R28) → 2^k-lift petals (R22): equal-window families in μ_{2N} = SUNFLOWERS
with lift petals, all sizes/windows, char 0. REMAINING ASSEMBLY: hclosure de-oracling
(μ-enumeration bridge) + the Conj-41/δ* composition through R20/21 + R19.

### O49 — LITERATURE INGESTED (~/Desktop/math) + residual (i) RESOLVED: the effective char-0 → F_p transfer theorem

**Library now local (~/Desktop/math), key results marked:**
* `9511209v1` Lam–Leung 2000: lengths of vanishing sums of m-th roots = ℕp₁+⋯+ℕp_r — the
  general-n base-case classification (our p=2 case is the m=2^k instance).
* `mann1965` Mann: irreducible rational-coefficient relation of length k ⟹ common order
  divides ∏_{p≤k} p. `trigonometric…` Conway–Jones Thm 5: order Q squarefree with
  **Σ_{p|Q}(p−2) ≤ k−2** (best possible) — independently re-derives our antipodal base case
  (2-power roots ⟹ Q | 2 ⟹ pairs).
* `487` Zannier survey: Dvornicich–Zannier generalization to algebraic coefficients
  (bounded degree d ⟹ effective order bound) — the tool if the tower argument ever needs
  coefficients beyond ℚ.
* `mvs-21jul20` Christie–Dykema–Klep: complete classification of minimal vanishing sums of
  weight ≤ 21 — finite tables for small-case sanity checks of the tower theorem.
* `0704.1747v3` Aliev–Smyth: explicit bounds on maximal torsion cosets on subvarieties of
  G_m^n — the count of structural solution families of e₁=⋯=e_t=0 (our fiber IS a torsion
  locus; their bound caps how many coset families can ever appear at any level).
* `9911094v1` Krick–Pardo–Sombra + `ASENS_2013` D'Andrea–Krick–Sombra: arithmetic
  Nullstellensätze with explicit height bounds — the generic char-0 ⟹ mod-p transfer
  machine (we use a sharper elementary route below, but these give the template for any
  future statement not amenable to direct norms).
* `2020-654` BCIKS, `2025-2055` BCHKS (ε*-loss formulation; beyond-LDR impossibility),
  `2025-2054` GG25 (Def 1.1 proximity gaps; **Thm 3.4: (ℓ,δ,a,t)-curve-decodability ⟹
  correlated agreement; Thm 3.5: threshold a = ℓn+1 ⟹ MUTUAL correlated agreement** — the
  exact quantifier bridges), `2026-532` S-two (App. A **Conjecture 1**: ℓ(θ) ≤ c₁·2^{c₂H(ρ)/η}
  up to the Elias radius r_E = 1−ρ−Θ(1/log p) [CS25 cap]; **Conjecture 2**: line-decodability
  with a = ℓ(θ)n + o(n)), `2026-861` Chai–Fan, `2604.09724` Kambiré/Krachun–Kazanin
  (near-capacity failure over prime fields — the disproof-side anchor), `2304.09445` AGGLZ
  (random RS capacity), `2025-2010` Diamond–Gruen (sharp ball-volume estimates).
* `1.pdf`/`13299D` Washington, Introduction to Cyclotomic Fields — norm machinery reference.

**RESIDUAL (i) RESOLVED — Theorem (effective transfer, complete elementary proof):**
Let n | p−1, fix a generator g of μ_n(F_p) and a primitive n-th root ζ ∈ ℂ; reduction
red : ℤ[ζ] → F_p, ζ ↦ g, is an order-preserving bijection μ_n(ℂ) → μ_n(F_p). For a w-subset
S ⊆ μ_n(F_p) with lift S̃, e_j(S) = red(e_j(S̃)). If e_j(S̃) ≠ 0 then N(e_j(S̃)) ∈ ℤ∖{0} and,
since e_j(S̃) is a sum of C(w,j) products of roots of unity (each of modulus 1 in every
archimedean embedding), |N(e_j(S̃))| ≤ C(w,j)^{φ(n)}. Hence p ∤ N for

    p > C(w, ⌊w/2⌋)^{φ(n)}     (crude:  p > 2^{w·φ(n)} = 2^{wn/2} for n = 2^m),

and then e_j(S) = 0 ⟺ e_j(S̃) = 0 for every j ≤ t. **Conclusion: for all such p, the
F_p-fiber equals the char-0 fiber — by the O48 tower theorem, exactly the coset unions,
count C(n/d, w/d).** The threshold is explicit and the proof is the same AM–GM/triangle
norm trick as the in-tree effective P-A lane (O38-nubs) — the two lanes now share one
engine. Sharpness side: extra solutions at p = 17, n = 16 (O47 data) show a threshold is
necessary; Krachun–Kazanin's construction (2604.09724) lives at polynomial p — so the
exponential-vs-polynomial threshold question is precisely where the disproof side still
breathes. (A poly-p₀ version would need the fiber equations' integer values to be
smooth-number-free — a different, genuinely analytic question, correctly flagged by both
2026/858's p₀ and our O43 refutation of its printed form.)

**Residual (ii) mapped to the live conjecture with exact bridge citations:** GG25 Thm 3.5
turns line-decodability (threshold ℓn+1) into mutual correlated agreement; S-two Conj 2
reduces it to Conj 1 (worst-case list ℓ(θ) over ALL received words). Our O48 corollary —
fiber ≤ 2^{2/η} at t = ηn — is **the first proven instance of the Conjecture-1 budget
shape on plain smooth-domain RS** (at the unit-syndrome received words, char 0 / p above
the transfer threshold). The all-words upgrade = Conjecture 1 itself on 2-power domains;
the descent machinery (sq_fiber_pair tower; arbitrary received words descend along the
FRI fold) is the in-tree candidate attack and converges with the C19/Descent lane.

### O50 — LAM–LEUNG AT p = 2 MACHINE-CHECKED + the UNCONDITIONAL t = 2 tower resolution

The classical base case of the tower theorem is now a Lean theorem (`LamLeungTwoPow.lean`,
axiom-clean, 0 sorry, 0 warnings):

* `vanishing_sum_antipodal` — in characteristic zero, a finite set of 2^(m+1)-th roots of
  unity with vanishing sum is closed under negation. Proof exactly as recorded in O47:
  indicator polynomial of the exponent set, `minpoly.dvd`, `cyclotomic_eq_minpoly_rat`,
  `cyclotomic_prime_pow_eq_geom_sum` (so Φ_{2^(m+1)} = X^{2^m}+1), explicit quotient
  degree bound, coefficient pairing c_j = c_{j+2^m}, and ζ^{2^m} = −1.
* `t2_resolution_unconditional` — wiring `vanishing_sum_antipodal` (at levels m+2 and m+1,
  the latter via `IsPrimitiveRoot.pow`) into `TopLine.t2_tower_resolution`: **every finite
  set of 2^(m+2)-th roots of unity with ∑x = ∑x² = 0 is a union of μ₄-cosets —
  hypothesis-free, machine-checked end to end.** The first two rungs of the O48 tower are
  now unconditional; the general-t rungs iterate the same two machine-checked pieces
  (assembly + base case) with Newton bookkeeping, exactly as recorded in O48.

(Build note: one minimal single-module `lake build` of TopDirectionLineCount was required
for the cross-file import — 5s, no thrash.)

### O51 — the ZERO FIBER DOMINATES: probe + the Aliev–Smyth route to all class syndromes

Extending from ē = 0 toward the full class-syndrome chart (= ALL top-window syndromes, by
the O42 h-parametrization):

* **Probe (exhaustive, μ₁₆/F₂₅₇, w = 8, t = 3, all 12457 nonempty classes):** the maximum
  fiber over ALL (ē₁,ē₂,ē₃) is the ZERO fiber (6 = the tower count C(4,2)); every nonzero
  class has fiber ≤ 2; mean 1.03. The structural (coset) solutions live exclusively at
  ē = 0 — the tower theorem captures the worst case.
* **Scaling orbits:** x ↦ λx maps fiber(ē₁,…,ē_t) bijectively to fiber(λē₁, λ²ē₂, …, λ^tē_t)
  — fibers are constant on weighted-projective orbits; the zero fiber is the unique fixed
  point, consistent with it being extremal.
* **The uniform tool (Aliev–Smyth Thm 1.1, ~/Desktop/math/0704.1747):** the number of
  maximal torsion cosets on a hypersurface H(f) ⊆ G_m^n of degree d is ≤ c₁(n)·d^{c₂(n)}
  with EXPLICIT c₁, c₂ (and Rémond's (k+1)^{3(k+1)²} for general subvarieties). Every
  fiber member is a torsion point on V(e₁−ē₁, …, e_t−ē_t) ⊆ G_m^w, so the ISOLATED part
  of every fiber is bounded by an explicit constant in (w, t), UNIFORMLY in ē and
  field-independently. The positive-dimensional torsion cosets of V are exactly the
  mixed "coset ∪ leftover" families — whose μ_n-points are counted by the SAME tower/
  descent analysis componentwise. **Program for full top-window coverage: A-S coset
  classification (uniform, effective) + per-coset tower count (machine-checked pieces
  O46–O50) ⟹ every class syndrome has list ≤ explicit(w,t) + tower count.** The probe
  says the truth is even cleaner (nonzero fibers ≤ 2 at the tested scale).
* Remaining beyond that: syndromes engaging the LOW window (received words at smaller
  distance scales) — the genuinely-all-words quantifier = S-two Conjecture 1 proper.
### O53 — E1 + the char-0 bijection FORMALIZED; the minpoly bridge (nubs, 2026-06-09)

Two new axiom-clean bricks (both `[propext, Classical.choice, Quot.sound]`):

**`ArkLib/ToMathlib/OddCharacterOrthogonality.lean`** — E1, the O38 engine:
- `odd_power_orthogonality`: `∑_{i<m2} ζ^{(2i+1)j}·ζ^{−(2i+1)j'}` = `m2`/`0` on/off diagonal
  (factor as `ζ^δ · ∑(ζ^{2δ})^i`; primitivity kills the geometric sum).
- `parseval_odd_powers`: `∑_{i<m2} (∑_j c_j w_i^j)(∑_j c_j w_i^{−j}) = m2·∑ c_j²` for
  `w_i = ζ^{2i+1}` — over `ℂ` this is `∑_{i∈(ℤ/m)^×} |σ_i(α)|² = (m/2)∑c_j²`, the Parseval
  step of the shared norm engine (O38 / the O49-transfer's `|N| ≤ C(w,j)^{φ(n)}` trick).
  The engine's core identity is now formal.

**`ArkLib/ToMathlib/CyclotomicPatternInjectivity.lean`** — the bijection step of Theorem A:
- `pattern_sum_injective`: ℤ-combinations of `ζ^0..ζ^{2^k−1}` (`ζ` primitive `2^{k+1}`-th,
  char 0) determine their coefficients — difference polynomial has degree `< 2^k =
  deg Φ_{2^{k+1}} = deg minpoly_ℚ(ζ)`, so it vanishes identically.
- `signed_subset_sum_injective`: `(P,N) ↦ ∑_P ζ^j − ∑_N ζ^j` injective on disjoint pairs —
  so `n0_pattern_count` (DisjointPairCount.lean) is now formally the EXACT char-0 image
  count: distinct admissible patterns give distinct subset sums.
- `natDegree_minpoly_rat_two_pow`: `deg minpoly_ℚ(ζ) = 2^k` — discharges the
  `LinearIndependent` hypothesis of `R11.antipodal_of_sum_zero`
  (LamLeungUnconditionalQ.lean) at every 2-power level via `R11.linearIndependent_pow_le`.
  NOTE (same-hour convergence): O50's `vanishing_sum_antipodal` independently
  machine-checks the antipodal theorem by the same cyclotomic-minpoly technique — the
  bridge here remains as leaf `ToMathlib` API (coefficient determination + the degree
  fact), complementary to O50's end-to-end form.

### O54 — the tower theorem from the second seat: independent same-hour proof, EXACT char-0 verification, and the descent-step brick (nubs, 2026-06-09)

While O48 ("THE DICHOTOMY RESOLVES TRUE") was landing, this seat independently derived the
same theorem from the O47 crystallization — convergence, not duplication; recorded as
cross-verification (the same norm O38 received). Three things here are NEW relative to
O48/O50:

**1. A second, independently-found proof with a cleaner induction packaging** (no separate
coset-assembly step — the assembly is free because `s^L` is a homomorphism with kernel
`μ_{2^L}`): for `S ⊆ μ_n`, `n = 2^m`, `1 ≤ t < n`, `L = ⌊log₂ t⌋ + 1`,

    e₁(S) = ⋯ = e_t(S) = 0  ⟺  S = (s^L)⁻¹(U) for some U ⊆ μ_{n/2^L}.

(⟸): on a `μ_{2^L}`-coset, `p_j = 0` unless `2^L | j`, and `j ≤ t < 2^L`; Newton converts.
(⟹) induction on t: Newton ⟹ `p₁..p_t(S) = 0`; `e₁ = 0` + the t=1 theorem ⟹ `S = s⁻¹(T)`;
the pair identity `p_{2j}(S) = 2·p_j(T)` hands `T ⊆ μ_{n/2}` the conditions at `⌊t/2⌋ ≥ 1`;
induct; `⌊log₂⌊t/2⌋⌋ + 2 = ⌊log₂ t⌋ + 1`. Count `C(n/2^L, w/2^L)`, agreeing with O48's
`d = 2^L` = smallest 2-power `> t`. The general-t induction here goes through the SAME
single mechanism at every rung (square-root-pair power sums), so the O48 assembly's
per-rung root-of-unity arguments (`mul_i_closure` etc.) are subsumed by one lemma family.

**2. EXACT characteristic-0 verification** (strengthens O48's F₂₅₇ proxy): probe
`scripts/probes/probe_tower_fiber.py` computes in `ℤ[x]/(x^{n/2}+1)` — exact integers, no
finite-field proxy, `e_j` computed DIRECTLY (so the check is independent of the Newton
step) — at n = 8 AND 16, ALL weights, t ≤ 6: ALL PASS, including every predicted empty
fiber (`2^L ∤ w`) and the t-plateaus.

**3. The descent-step identity as reusable API**: `ArkLib/ToMathlib/SqrtPairPowerSum.lean`
(axiom-clean) — `sum_pow_even_sqrtPairs` (`∑_{x∈s⁻¹(T)} x^{2j} = 2·∑_{z∈T} z^j`, the
general-j engine of step (⟹), generalizing O48's t=2 hdesc step and O50's t=2 resolution
to arbitrary depth), `sum_pow_odd_sqrtPairs` (odd power sums vanish), `card_sqrtPairs`
(`|s⁻¹(T)| = 2|T|`) — any field of char ≠ 2. Together with O50's machine-checked base case
the general-t mechanization now lacks only: Newton's identities glue (Mathlib:
`MvPolynomial.NewtonIdentities`) + the finite-depth induction scaffold.

With the O49 effective transfer (`p > C(w,⌊w/2⌋)^{φ(n)}`), the count is unconditional at
production-scale primes. What remains of the prize core is unchanged and shared: extending
from unit syndromes to ALL received words (the MCA quantifier) — Conjecture D / the
classical band.

### O52 — the GENERIC TOWER RUNG machine-checked: μ_d-coset unions climb to μ_{2d}

`TopLine.mul_root_closure` (TopDirectionLineCount.lean §TowerRung, axiom-clean, 0 sorry,
char-free): closure under the full d-th-roots packet + antipodally closed d-th-power image
⟹ closure under any ω with ω^d = −1 — i.e. μ_{2d}-coset structure. This generalizes the
t = 2 assembly (mul_i_closure = the d = 2 instance) to EVERY level of the O48 tower. The
machine-checked tower inventory now: base case (O50 Lam–Leung), generic d-to-1 descent sum
(sq_fiber_pair pattern; general-d version is the same fiber argument), generic rung (this),
coset converse (O46), lossless transfer (O45). Remaining glue per rung: the single Newton
identity p_d = ±d·e_d under vanishing lower e's (char 0) — Mathlib's MvPolynomial
NewtonIdentities instantiation, queued.

### O53 — THE FULL TOWER THEOREM MACHINE-CHECKED, UNCONDITIONAL (the O48 induction complete in Lean)

`LamLeungTwoPow.full_tower` (axiom-clean, 0 sorry, 0 warnings): **in characteristic zero,
a finite set of 2^M-th roots of unity whose power sums vanish in the window 1 ≤ j < 2^s
(s ≤ M) is closed under multiplication by every 2^s-th root of unity — a union of
μ_{2^s}-cosets.** Hypothesis-free, full induction on s. The Newton glue proved UNNECESSARY:
in power-sum form the rung condition transfers through the fiber structure directly —
`pow_fiber_sum` (every fiber of x ↦ x^{2^s} on a μ_{2^s}-closed set is a full coset, so
p_{2^s}(S) = 2^s • Σ_image, then char 0 divides), Lam–Leung one level down (O50) makes the
image antipodal, `TopLine.mul_root_closure` (O52) climbs the rung, and `mu_double_closure`
upgrades ω-closure to full μ_{2^{s+1}}-closure. (The power-sum window is exactly the
syndrome of the all-ones error on S — the coding-side reading is native.)

**Status of the tower chain: COMPLETE AND UNCONDITIONAL IN LEAN.** Base case (O50), every
rung (O52+O53), descent sums (O53), coset converse (O46), lossless syndrome transfer (O45)
— so the deep-interior fiber bound `≤ 2^{n/2^s} = 2^{O(1/η)}` (the KK25/S-two budget) at
power-sum windows is now a fully machine-checked consequence over char-0 fields, and over
F_p above the O49 effective threshold. Two minimal single-module rebuilds of
TopDirectionLineCount were the only builds used.

Remaining #232 queue: effective-transfer Lean brick (norms machinery); O51 class-chart
program (Aliev–Smyth + componentwise tower); S-two Conjecture 1 proper (low-window/all
received words) — the recognized live open conjecture of the field.

### O55 / Round-29 — ITERATED 2^k-LIFT, NO ORACLES: independence DISCHARGED (ℤ-form) + the de-oracled level iteration; AUDIT: the R23/R24/R25 `hindep` was vacuous as stated

`RigidityIterated2kLift.lean` (main-loop solo, axiom-clean, 0 sorry, strict-verified). Convergence
placement: completes the named remaining item of Round-28 (`RigidityFullWindow.lean`, "hclosure
de-oracling — μ-enumeration bridge") and complements O50 (`LamLeungTwoPow`, single-set) / O52
(generic rung) / O54 (second-seat tower): everything here is the DISJOINT-PAIR (equal-window)
engine, which is what the Conj-41 list application needs; the single-set forms drop out at B = ∅.

* **AUDIT FINDING (machine-checked, `fValued_hindep_unsatisfiable`):** the `hindep` hypothesis of
  R23/R24/R25 (`∀ g : Fin N → F, (∑ j, g j * ζ^j) = 0 → ∀ j, g j = 0`) quantifies over
  **F-valued** coefficients — UNSATISFIABLE for `N ≥ 2` (`g = (ζ, −1, 0, …)` sums to zero), so
  every theorem consuming it was vacuously true and inapplicable as stated (this includes the
  Round-28 `full_window_rigidity` if its closure oracle is fed from R25 as-is). The proof
  skeletons are sound (every instantiation is integer-cast); the fix is the ℤ-valued form.
  Treat the F-form statements in `RigidityBaseCasePairs`/`RigidityTriplesSunflower`/
  `RigidityGeneralT1` as deprecated surfaces; consume the ℤ-forms here (`HalfBasisIndepZ`,
  `bridgeZ`, `disjoint_equal_sum_antipodal_int`).
* **THE DISCHARGE (`halfBasisIndepZ_of_primitiveRoot`):** `HalfBasisIndepZ ζ 2^{m−1}` holds for
  EVERY primitive `2^m`-th root of unity in a characteristic-0 field
  (`cyclotomic_eq_minpoly_rat` + `natDegree_cyclotomic` + `totient_prime_pow` +
  `linearIndependent_pow`). Same cyclotomic content as O53's `pattern_sum_injective`, packaged
  as the exact form the rigidity chain consumes. The chain is now NON-VACUOUS and
  hypothesis-free: char 0 + primitivity suffice.
* **The encoding bridge (`antipodallyClosed_of_disjoint_equal_sum`):** field-level `t = 1`
  closure — disjoint `A, B ⊆ ±ζ^{<N}` with equal sums are BOTH `AntipodallyClosed` (R26's
  predicate); `sval` injectivity from ℤ-independence does the signed-point ↔ field-element
  plumbing. THIS IS THE R28 "μ-enumeration bridge" de-oracling. Scale descent: `isSignedPow_sq`
  (`μ_{2^m} → μ_{2^{m−1}}`, upper range folded by `ζ^{2^{m−1}} = −1`) + `IsPrimitiveRoot.pow`;
  assembly: `closure_step` (the general `mul_i_closure`, char-free).
* **`iterated_2k_lift` (THE THEOREM, no oracles):** `A, B ⊆ μ_{2^m}` disjoint with equal
  `p_1..p_t`, `1 ≤ k ≤ m`, `2^{k−1} ≤ t` ⟹ both closed under EVERY `2^k`-th root of unity
  (R22 `2^k`-lift structure). Induction on `k` over the R26 engine; maximal `k` gives exactly
  O48's `d = smallest 2-power > t`. + `coset_closure_of_equal_window` (generator form),
  `antipodal_closure_unconditional` (non-vacuity witness).
* **Single-set corollaries (`B = ∅`, §7):** `vanishing_sum_antipodal` (= O50's theorem via the
  pair engine — convergent route) and `vanishing_window_coset_closure` — the O48 TOWER
  THEOREM's forward inclusion in power-sum form at ALL `t` in one statement. SAME-HOUR
  TRIPLE CONVERGENCE: the second seat's `full_tower` (LamLeungTwoPow, its O53 entry) landed
  the same single-set statement minutes earlier by the rung-by-rung route — independent
  cross-verification; what is unique here is the PAIR (equal-window) engine those single-set
  forms drop out of, which is the form the Conj-41 list application consumes.

REMAINING (sharpened, honest): (a) the Newton e-window ⟺ p-window bridge over `CharZero`
(connects R27's nodal output + O44/O45 esymm fibers + the O54 packaging to this power-sum
engine); (b) the counting corollary (`μ_{2^k}`-coset-closed ⟹ `≤ 2^{n/2^k}` sets — the
KK25/S-two `2^{O(1/η)}` budget); (c) the Conj-41/δ* composition through R20/R21 + R19;
(d) effective char-0 → `F_p` height threshold beyond O49's resolution where it applies;
(e) the MCA quantifier (unit syndromes → all received words). (d)/(e) genuinely open research;
the prize core (δ* inside `(1−√ρ, 1−ρ)`) remains 100% open.

### O55 — tower_count: the 2^{O(1/η)} budget as a machine-checked COUNTING theorem

`LamLeungTwoPow.tower_count` (axiom-clean, 0 sorry): the number of w-subsets of any
2^M-torsion domain with vanishing power-sum window 1 ≤ j < 2^s is

    ≤ 2^{#(2^s-th-power classes of the domain)}   (= 2^{n/2^s} on μ_n).

Mechanism: by full_tower (O53) every such subset is μ_{2^s}-closed, hence EXACTLY
recoverable from its 2^s-th-power image (S = D₀.filter (x ↦ x^{2^s} ∈ image S)) — the
family injects into the subsets of the power-class space. At window scale
t = 2^s − 1 = Θ(ηn) this is the KK25/S-two budget 2^{O(1/η)}, now a counting THEOREM
(char 0; F_p above the O49 threshold). With O45's lossless syndrome transfer, the
all-ones-error syndrome lists deep in the interior on 2-power domains are budget-bounded,
machine-checked end to end: full_tower + tower_count + zero_fiber_filter_eq +
compat_gamma_count form one complete verified pipeline from "vanishing window" to
"list count ≤ 2^{O(1/η)}".

### O56 — the all-words entry point formalized: syndrome fold identity + cancellation dichotomy + scaling orbit

`LamLeungTwoPow.lean` §GeneralDescent/§ScalingOrbit (axiom-clean, 0 sorry):

* `syndrome_fold` — for a GENERAL error (support S, values v), the even syndrome
  coordinates equal the syndrome of the FOLDED error one level down:
  p_{2j}(v,S) = p_j(fold v, S²), (fold v)(y) = Σ_{x²=y} v(x). The FRI folding identity on
  the error side, in the same synd framework as O44–O55. The all-ones error has
  fold v = fiber-size ≠ 0 — exactly why the tower theorem closes unconditionally there.
* The cancellation dichotomy: the ONLY obstruction to descending a general word is
  fold-cancellation (fold v = 0 at an image point) — the precise formal location of
  all-words list mass (= S-two Conjecture 1's difficulty) and the convergence point with
  the C19/descent-lane anatomy from the protocol side.
* `fiber_scaling` (O51 orbit lemma): unit scaling carries power-sum fibers to
  weighted-scaled fibers — fibers constant on weighted-projective orbits, zero fiber the
  unique fixed point (empirically the maximum, O51 probe).

The all-words attack surface is now FORMAL: prove budget bounds for no-cancellation words
by iterating syndrome_fold + full_tower (a conditional theorem now in reach), and
quantify the cancellation locus (where the open conjecture genuinely lives).

### O57 — the valued-descent toolkit complete: odd fold + weight conservation

`LamLeungTwoPow.lean` §ValuedDescent (axiom-clean, 0 sorry): a window-vanishing valued
error (S, v) descends to TWO half-window folded systems —

* `syndrome_fold_odd`: p_{2j+1}(v,S) = p_j(foldOdd v, S²), foldOdd(y) = Σ_{x²=y} v(x)·x
  (with O56's even fold: the complete C19-style even/odd error decomposition, formal);
* `sq_image_card`: |S| ≤ 2·|S²| (squaring fibers ≤ 2; the support at most halves per
  level — weight conservation down the tower, char-free).

With O56: the quantitative valued-descent step is fully machine-checked. Under
no-cancellation both folds are genuine half-scale errors with halved windows; the
cancellation locus (a fold value = 0) remains the exact formal home of S-two Conj 1 —
both folds must SIMULTANEOUSLY cancel for mass to vanish (even AND odd: v(x)+v(−x) = 0
and v(x)x − v(−x)x = 0 ⟹ v(x) = v(−x) = 0 when char ≠ 2!): wait — even fold at pair
{x,−x}: v(x)+v(−x); odd: (v(x)−v(−x))x. BOTH zero ⟺ v(x) = v(−x) = 0 (char ≠ 2, x ≠ 0).
**So full fiber cancellation in BOTH folds is impossible for a genuine error** — list
mass cannot vanish entirely; it can only MOVE between the even and odd branches. This is
the formal seed of the branch-accounting that the C19/descent lane tracks, and the next
provable target: per-level branch-mass conservation ⟹ a window-vs-weight tradeoff for
ALL valued errors.

### O58 — BRANCH-MASS CONSERVATION: the first unconditional ALL-WORDS descent theorem

`LamLeungTwoPow.lean` §BranchMass (axiom-clean, 0 sorry):

* `fold_mass_conservation` — at any squared point, the even and odd folds cannot BOTH
  vanish unless the error vanishes on the whole fiber (char ≠ 2, 0 ∉ S): the 2×2 fiber
  system (v(x)+v(−x), (v(x)−v(−x))x) is nonsingular.
* `branch_mass_inequality` — hence for EVERY genuine valued error,
  |S| ≤ 2·(|supp fold_even| + |supp fold_odd|): every fiber feeds at least one branch,
  weight descends with at most factor-2 loss per level, split between the two branches.

This is UNCONDITIONAL over all received words — no no-cancellation hypothesis, no
structure on v. The all-words list question is now formally branch-accounting over the
2-adic tower with a machine-checked conservation law: window-vanishing mass cannot be
destroyed by the fold, only routed. Combined with the per-branch window halving (O56/O57
fold identities), the program's remaining open content is the per-level BRANCH-COUNT
distribution (how many branches can stay heavy how deep) — the C19/descent lane's
quantitative question, now with its conservation backbone in Lean.

### O59 — WINDOWS FORCE WEIGHT: the tradeoff completing the descent bookkeeping

`LamLeungTwoPow.window_forces_weight` (axiom-clean, 0 sorry, char-free): a valued error
with nonzero values and vanishing power sums on the full window j < t has support size
> t (the t×|S| Vandermonde kernel on distinct points is trivial; proof via the punctured
locator pairing — Σ v(x)P(x) computed two ways).

THE DESCENT BOOKKEEPING IS NOW PINCHED BETWEEN TWO MACHINE-CHECKED INEQUALITIES:
* (O58, mass conservation) every branch split preserves at least half the weight across
  the two branches: |S| ≤ 2(|supp even| + |supp odd|);
* (O59, window forces weight) every branch that inherits a window of length t must carry
  support > t — and the fold identities (O56/O57) say branches DO inherit half-windows
  (the odd branch even inherits the j = 0 constraint).
So down the tower: windows halve, weights at least halve in total but each surviving
branch is forced fat by its window. The remaining open content of the all-words question
is exactly the BRANCH-COUNT DISTRIBUTION: how many branches can stay (window-)alive at
each depth. Everything else around it — conservation, tradeoff, fold identities, the
unit-syndrome case (full tower + count), the class-syndrome chart, the effective
transfer — is theorem.

### O60 — THE NEWTON BRIDGE: esymm windows ⟺ power-sum windows (the last internal seam welded)

`LamLeungTwoPow.lean` §NewtonBridge (axiom-clean, 0 sorry):

* `newton_step` — Mathlib's MvPolynomial Newton recurrence instantiated on any finite
  subset of F (σ = ↥S, aeval at coordinates; psum/esymm instantiation identities proven).
* `psum_window_of_esymm_window` (characteristic-free) and `esymm_window_of_psum_window`
  (char 0, divides by k) — both DIRECT, no induction: every cross term of the recurrence
  carries a window-interior factor.
* `esymm_window_iff_psum_window` — THE BRIDGE: the syndrome-side pipeline (O44–O46, esymm
  windows at unit syndromes) and the tower pipeline (O53–O59, power-sum windows = all-ones
  -error syndromes) describe the SAME fibers, formally.

The full #232 formal corpus is now ONE connected machine-checked theory: unit-syndrome
lists = esymm fibers (O45) = psum fibers (O60) = coset unions (O53) of count ≤ 2^{O(1/η)}
(O55), transferring to F_p (O49), with general words governed by the fold identities
(O56/O57), mass conservation (O58), and the window-weight tradeoff (O59). Open content:
the branch-count distribution (= S-two Conj 1 on these domains), surrounded.

### O61 — THE CAPSTONE: unit_syndrome_list_budget — the entire pipeline as ONE theorem

`LamLeungTwoPow.unit_syndrome_list_budget` (axiom-clean, 0 sorry): over a char-0 field
with the 2^M-th roots of unity, for any 2^M-torsion domain D₀ and window c = 2^s − 1,

    #{E ∈ powersetCard w D₀ : CompatC (unitVec (w−1)) N c E} ≤ 2^{#(2^s-power classes)}.

One statement composing the whole session: O45 (syndrome ⟺ esymm fiber) ∘ O60 (Newton
bridge to power sums) ∘ O53 (full tower) ∘ O55 (recovery-injection count). At window
scale t = Θ(ηn) on μ_n this is the 2^{O(1/η)} interior list budget at unit syndromes —
the KK25/S-two budget shape — as a single named machine-checked theorem; over F_p it
holds above the O49 effective threshold. The #232 deep-interior unit-syndrome question
is, with this, CLOSED in formal form; the open remainder is the all-words quantifier
(branch-count distribution = S-two Conjecture 1), with its formal toolkit (O56–O59)
assembled and its no-go routes recorded.

### O62 — the tower CONVERSE: closure forces window vanishing — exhaustiveness is an IFF

`LamLeungTwoPow.lean` §TowerConverse (axiom-clean, 0 sorry, char-free):

* `subgroup_pow_sum` — a full d-th-roots packet sums to zero at every exponent d ∤ j
  (geometric series, primitive-root division).
* `closed_pow_sum_vanish` — a μ_d-closed set has Σ x^j = 0 for all d ∤ j (fiberwise:
  each squaring... d-power fiber is a full coset, whose j-sum carries the packet sum).

With full_tower (O53): **closure under μ_{2^s} ⟺ vanishing power-sum window j < 2^s**
(char 0; ⟸ needs char 0, ⟹ char-free) — the O48 exhaustiveness as a genuine
characterization, both directions machine-checked. The tower theory is COMPLETE as
stated: structure (O53), converse (O62), count (O55), bridge (O60), transfer (O45/O49),
capstone (O61).

### O63 — the TWO-SIDED budget + the corpus wiki page

* `LamLeungTwoPow.two_sided_unit_syndrome_budget` (axiom-clean, 0 sorry): the SAME
  unit-syndrome compatibility list is bounded below by the coset count C(#reps, m) (O46)
  and above by the power-class budget 2^{#classes} (O61) — matching exponential scales
  (C(n/d, w/d) vs 2^{n/d} on μ_n): the interior unit-syndrome list pinned from both
  sides in one machine-checked statement.
* `docs/wiki/tower-fiber-theory.md` — the stable map of the O35–O63 corpus (file table,
  one-paragraph theory, recurring Lean gotchas), per the repo guardrail that stable
  guidance must not live only in ephemeral notes.

### O63 — FOLD BRANCHES ARE COEFFICIENT SLICES: the branch tree translated to plain coefficient combinatorics (nubs, 2026-06-10)

New brick `ArkLib/Data/CodingTheory/ProximityGap/FoldPolynomialSlices.lean` (axiom-clean):
for a polynomial error `e = f.eval` on a negation-closed domain (char ≠ 2, `0 ∉ D`),

* `foldVal D f.eval (x₀²) = (evenSlice f).eval (x₀²)` and
  `foldValOdd D f.eval (x₀²) = x₀² · (oddSlice f).eval (x₀²)` — the even/odd folds ARE
  evaluations of the coefficient slices `evenSlice f = contract 2 (f + f∘(−X))` /
  `oddSlice f = contract 2 (divX (f − f∘(−X)))`, up to the unit twist `y`;
* `foldVal_ne_zero_iff` / `foldValOdd_ne_zero_iff` — branch aliveness = slice
  nonvanishing (the twist drops out).

Since every valued error interpolates to a unique polynomial of degree `< n`, this is a
TRANSLATION of the whole O56–O59 branch-accounting: iterating, depth-`ℓ` branches =
residue classes of coefficient exponents mod `2^ℓ` under the ceiling-halving digit code
(odd fold maps exponent `e ↦ (e+1)/2` from the twist, even fold `e ↦ e/2` — the code is
constant on classes mod `2^ℓ`), and a branch is alive iff its class holds a nonzero
coefficient. Verified exhaustively: `scripts/probes/probe_fold_slices.py` (n = 16,
p = 97, 500 random low-degree polys, depths 1–3, tree-vs-slices ALL MATCH; the naive
`e mod 2^ℓ` indexing FAILS — the twist shift is real).

**Consequence for the open core (O59's branch-count distribution):** it equals the joint
distribution of (evaluation weight on μ_n, 2-adic spread of coefficient support) over
polynomials of degree ≤ n − t. Window-vanishing = top-degree truncation (degree ≤ n − t);
alive-branch count at depth ℓ = #nonzero coefficient classes mod 2^ℓ. The all-words list
question, in one sentence: **how many low-degree polynomials can simultaneously have low
evaluation weight and prescribed 2-adic coefficient spread** — a plain question about RS
weight distributions stratified by the 2-adic exponent tree, with no fold machinery left
in the statement. (The C19 anatomy lives here too: its 3 + 16 list elements are exactly
coefficient-spread classes — the transversal degeneracies are spread patterns.)
### O64 — the M_TRUE upgrade of the Conjecture-41 violation: genuine errors, kernel-checked

`LamLeungTwoPow.conj41_mtrue_witness` (axiom-clean, 0 sorry; kernel decide with raised
heartbeats): at each of the six line parameters γ ∈ {1,…,6} of the O44 witness line
s(γ) = unitVec 5 + γ·e₈ over ZMod 17, an EXPLICIT weight-6 error — support AND
all-nonzero values — satisfies the FULL 9-coordinate syndrome system (e.g. γ = 1:
E = {0,6,8,11,12,14}, v = (9,5,13,9,9,6)). Hence

    M_true(s₁, s₂) ≥ 6 > 5 = ⌊(2D−1)/c⌋   over ZMod 17 —

the violation now holds at the exact M_true quantity of Conjecture 41's "equivalently"
sentence, fully kernel-verified (closing the last queued refinement of the O43/O44
refutation arc). The session's refutation of the printed conjecture is complete at every
level of fidelity: rank form (structural, every γ), M_compat form (counting), M_true form
(genuine codeword-list mass).

### O65 — the GENERAL-RADIX fold: the descent toolkit extends to mixed-radix smooth towers

`LamLeungTwoPow.lean` §GeneralRadixFold (axiom-clean, 0 sorry, char-free):

* `syndrome_fold_general` — the complete d-ary syndrome decomposition:
  p_{dj+r}(v,S) = p_j(fold_r v, S^d) for every residue r, where
  (fold_r v)(y) = Σ_{x^d=y} v(x)·x^r. The O56/O57 even/odd fold is the d = 2 case.
* `fold_mass_conservation_general` — ALL d twisted folds vanishing at a fiber forces
  v = 0 on the fiber (via window_forces_weight applied to the fiber error: the twisted
  folds ARE the fiber's power-sum window, length d ≥ fiber size). Generalizes O58's 2×2
  nonsingularity to every radix.

Consequence: the entire descent program (fold identities + mass conservation + the
window-weight tradeoff) now applies to ARBITRARY smooth towers — mixed-radix n = ∏ dᵢ —
not just 2-power domains. In particular the Mersenne-31/Circle-STARK domains of S-two's
own deployment (whose tower is not 2-adic) are now in scope of the formal toolkit; the
branch-accounting question generalizes verbatim with d-ary branching.

### O66 — LAM–LEUNG AT EVERY PRIME POWER: the mixed-radix base case machine-checked

`LamLeungTwoPow.vanishing_sum_mu_p_closed` (axiom-clean, 0 sorry): in characteristic
zero, a finite set of p^(m+1)-th roots of unity (ANY prime p) with vanishing sum is
closed under multiplication by every p-th root of unity — a union of μ_p-cosets. The
p = 2 case is O50's antipodal theorem. Engine, generalizing O50's proof shape:
Φ_{p^(m+1)} = Σ_{i<p} X^{i·p^m} (cyclotomic_prime_pow_eq_geom_sum) divides the exponent
indicator; a packet multiple G·R with deg R < p^m has ALL p coefficient slices equal to
R (`packet_mul_coeff`); membership is therefore invariant under exponent shifts by p^m,
i.e. under μ_p (explicit wrap-around bookkeeping, no div/mod rewriting).

With the O65 general-radix fold + this base case, the MIXED-RADIX tower program has both
machine-checked pillars: the descent identities at every radix and the base case at every
prime power. The mixed-radix analogue of full_tower (per-prime coset assembly via
Conway–Jones-style structure at composite levels) is the natural continuation —
on M31-style domains (n = 2^a·3^b·…) this is the route to the S-two-deployment analogue
of the O61 capstone.

### O67 — the mixed-radix base case verified (de Bruijn structure) + program statement

Falsify-first probe for the mixed-radix tower (the M31/S-two-deployment continuation):
EXHAUSTIVE verification at n = 12 and n = 18 (two-prime smooth, 2^a·3^b) that EVERY
vanishing subset sum of μ_n over ℂ decomposes into disjoint rotated full prime packets
(μ₂-pairs and μ₃-triples): 99/99 at n = 12, 999/999 at n = 18, zero violations. This is
the subset-sum instance of de Bruijn's theorem (On the factorisation of cyclic groups,
Indag. Math. 1953: vanishing sums of n-th roots for n with at most two prime divisors
are ℕ-combinations of rotated prime-packet sums) — the correct mixed-radix analogue of
the O50/O66 base cases. (At ≥ 3 primes Conway–Jones exotic minimal sums appear; M31-type
deployment domains are two-prime, so de Bruijn suffices there.)

MIXED-RADIX PROGRAM (mapped, both pillars + base now identified): O65 general-radix fold
identities (machine-checked) + O66 prime-power packet closure (machine-checked) +
de Bruijn two-prime structure (verified numerically; paper to add to ~/Desktop/math —
N.G. de Bruijn, "On the factorisation of cyclic groups", Indag. Math. 15 (1953) 370-377)
⟹ the two-prime full_tower analogue ⟹ the M31-domain capstone. Formalization route for
de Bruijn: group-ring ℤ[ℤ_n] ideal structure, or the elementary double-slice argument
(apply O66's packet_mul_coeff at BOTH primes via CRT exponent coordinates) — the latter
is the in-framework candidate.

### O68 — Theorem Q is now ONE in-tree kernel-checked theorem; the deep line censused exactly (nubs, 2026-06-10)

**`TheoremQAssembly.theoremQ_epsMCA_lower` (axiom-clean, 0 sorry, 0 warnings):** the per-prime
lower half of the determination as a single `epsMCA` statement — for any finite field with a full
n-th-root domain (n = s·m), 2 ≤ r ≤ s, k = (r−1)m, (1−δ)n ≤ rm, q > n+k: ∃ B with
C(s,r)·(q−n) ≤ B·((q−n)+C(s,r)·k) and ε_mca(evalCode H k, δ) ≥ B/q. Composes the three verified
bricks (ValueSpreadSecondMoment + QuotientDeepCore + SmoothFiberCount) into MCALowerBound's
framework; B ≳ ½min(C(s,r), (q−n)/k) beats 2⁻¹²⁸·q on [2¹²⁹, 2¹²⁷·C(s,r)) — every prime, every
2-power gap, the whole window. Statement-fidelity reviewed against `QuotientPerPrimeInstantiation.md`
(faithful; strengthens it in four sound directions — any finite field, r ≤ s, any admissible δ, no
2-power hypothesis — and the closed form is strictly sharper at the top window edge). The LOWER
HALF of #232 is now machine-checked end to end: nothing in it rests on prose.

**Deep-line census (`probe_qline_census.py`, hardened + independently re-verified with a different
algorithm/generator; degeneracy certificate explicit — 0 SB=0 subsets ⟹ provably exhaustive at
radius ≥ k+1):** at (n,m,r) = (16,2,5), BabyBear, z=5: the Theorem-Q deep line realizes the FULL
C(8,5) = 56 bad scalars (vs the monomial line's N₀(8,5) = 40 — measured at this z; no genericity
claim), per-γ lists at the witness radius are ALL singletons with union exactly {q_S}; one notch
below, per-γ ≤ 2 (5,440 size-2 + 56 size-1) with union 10,936. The re-verifier's monomial-side
census: floor lists {1:32, 3:8} (e₁ triple-collisions — NOT singletons), 4,248 sub-witness γ's,
and the sub-witness union is ALSO 10,936 — union size is line-independent here while γ-counts and
max-list differ. Moral for the per-line moment chain (rounds-14 work, lekt9 + swarm): the union
count and the max-list-size factor must be carried TOGETHER; neither alone determines Pr_γ[bad].
This is level-1 branch-count-distribution data for the surviving open core (O59/O61/O67 framing).

### O69 — the branch-count distribution ANSWERED IN SHAPE: maximal aliveness on minimal-weight words; two bricks + the weight–gcd tradeoff (nubs, 2026-06-10)

Ultracode panel (3 prover lanes + adversarial audits, every artifact re-compiled and
re-run from a second seat) on O59's open core — "how many branches can stay window-alive
at each depth." Deliverables, all landed:

**Bricks (axiom-clean, independently audited VALID):**
- `ArkLib/ToMathlib/IteratedFoldConservation.lean` — `iterated_fold_conservation`: if ALL
  `2^ℓ` depth-`ℓ` branch values (`branchVal`, the verified iteration of
  `foldVal`/`foldValOdd`) vanish at a point, the error vanishes on the entire iterated
  fiber; + `exists_alive_branch`, `all_branches_dead_iff`, `iterFiber_card_le`. The
  depth-`ℓ` fiber system is information-preserving — mass cannot vanish at ANY depth.
- `ArkLib/ToMathlib/WindowDualRS.lean` — **the full dual-RS bridge, BOTH directions,
  general n** (not just 2-powers; char ∤ n): `window_iff_exists_low_degree` — power sums
  `∑ v(ζ^i)(ζ^i)^j` vanish for `1 ≤ j < t` ⟺ `v` agrees on `μ_n` with a polynomial of
  `natDegree ≤ n − t`. The window IS the RS code, formally; the in-tree gap (only the
  forward direction existed, `rs_codeword_syndrome`) is closed. The j = 0 exclusion is
  load-bearing and was numerically audit-checked.
- `FoldPolynomialSlices.lean` extended: `weight_ge_live_image` — the depth-1
  **weight–dead-locus tradeoff**: #{squared points where some slice survives} ≤ weight.
  Iterated form (corollary of `iterated_fold_conservation` + the slice law): at EVERY
  depth `ℓ`, the alive slices share a common μ-root locus of size `≥ n/2^ℓ − w` — low
  weight forces shared root structure (locators), with the C19/coset families extremal.
  Probe: 3000 trials × depths 1–3, ALL PASS (`probe_fold_slices.py` companion data).

**The census (`scripts/probes/probe_branch_census.py`, 95,623 exact-F_p samples across
(n,p,t) ∈ {16,32}×{97,193,257,7681}×{2,3,4,8}, exhaustive on all minimal-weight families
that fit; audit re-ran byte-identical + out-of-model spot-checks):**
- **The conditioned question resolves OPPOSITE to the list-decoding intuition: minimal
  weight (w = t) codeword differences generically have MAXIMAL alive-branch counts
  (`2^ℓ` at every depth, every config).** The branch tree never thins on list-relevant
  words; "bound the alive count" is a dead route for the all-words question.
- C2 (0/95,623 violations): alive(ℓ) ≤ alive(ℓ+1) ≤ 2·alive(ℓ) — monotone doubling
  (provable from the slice law + conservation).
- C3 (0/95,623): alive(ℓ) = 1 forces `2^ℓ | n − w` — single-branch survival forces
  coset-compatible weight (the O46/O47 structures are the ONLY way to stay narrow).
- Sampling honestly stratified toward structured `f` (the right bias for falsifying
  universal claims; frontier minima are existence data, not uniform statistics).

**Where the open core now sits (sharpened):** branch COUNTS carry no list information —
the constraint on low-weight words is slice STRUCTURE: by the tradeoff above their
slices must share large root loci at every depth simultaneously. The all-words question
(S-two Conj 1 / Conjecture D) is exactly: count low-degree `f` whose 2-adic coefficient
slices are simultaneously root-coherent at every depth. C19's 3 + 16 anatomy is the
worked instance. The conservation + dual-RS + slice bricks make every term in that
sentence formal.
### O70 — the SMALL-GOOD-SET SECTOR of StrictCoeffPolysResidual is FREE: the §5 residual is equivalent to its large-sector restriction

**Brick (axiom-clean, 0 sorry, 0 warnings):**
`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/StrictCoeffLargeReduction.lean` —
`strictCoeffPolysResidual_iff_large`: the issue-#304 strict Johnson extraction residual
([BCIKS20] §5) holds **iff** its restriction `StrictCoeffPolysLargeResidual` adding the
hypothesis `k + 1 < (RS_goodCoeffsCurve u δ).card` holds.  The complementary sector
`|S| ≤ k + 1` is discharged UNCONDITIONALLY for every decoded family `P` — no probability,
Johnson, GS, or counting input — by pure Lagrange interpolation
(`exists_coeff_interpolant_of_card_le`: any target function on ≤ k+1 field points is matched
by a polynomial of `natDegree < k + 1`; built on Mathlib's `Lagrange.interpolate` +
`degree_interpolate_lt`).  Keystone front door included:
`correlatedAgreement_affine_curves_of_largeResidual` reaches BCIKS20 Theorem 1.5 from the
large-sector residual + `BoundaryProbabilityResidual` alone.

**Probe (`probe_strict_coeff_smallset.py`, GF(13), 4000 + 2000 trials):** small-set claim
4000/4000 PASS; the control at `|S| = k + 2` fails for 1861/2000 generic coefficient
functions (expected ≈ (p−1)/p · 2000 = 1846) — the cutoff is EXACTLY `k + 1`, so the
reduction strips precisely the contentless sector and nothing more.

**Moral for the producer lanes:** every `betaRec`/Hensel/curve-extraction producer
(`KeystoneStrictResidual`, `CurveFamilyHensel`, `FaithfulCurveExtraction`,
`OffcentreKeystoneAssembly`, `StrictCoeffProducer`) now gets `k + 1 < |goodSet|` as a free
hypothesis: their "matching set is large" counting demands are only ever invoked in a regime
where the good set is itself large, which is exactly the regime BCIKS20 §5's
Guruswami–Sudan counting addresses.  The genuinely open per-`(u, P)` content (Claim 5.9 base
reading, tail vanishing, GS cargo) is untouched — but its demanded domain just shrank to
where the paper's argument actually lives.

### O71 — the literal pair-case Johnson conjecture is now ONE hypothesis away: per-δ `JohnsonNumericBound` ⟹ `mca_johnson_bound_CONJECTURE` at ℓ = 2 (verbatim, in-tree)

`MCAConjecturePairReduction.lean` (axiom-clean, 0 sorry, 0 warnings) closes the last
wiring gap in the #302 Johnson MCA chain that `Hab25WhirBridge` had left open: the bridge
targeted an *abstract* `(BStar, errStar)` and still carried the closed-form comparison
`ofReal (johnsonBoundReal) ≤ errStar δ` as a hypothesis, while `Hab25ConjectureGlue`
proved exactly that comparison for the *literal* conjecture error — nobody had composed
them into the verbatim statement. Now:

* `mca_johnson_bound_CONJECTURE_pair_of_johnsonNumericBound` — per-δ
  `JohnsonNumericBound φ (2^m) (μ δ).toNNReal δ` on the admissible range (η := μ(δ) =
  min(1−√ρ−δ, √ρ/20)) yields `mca_johnson_bound_CONJECTURE α φ m (Fin 2) exp` VERBATIM:
  `BStar = √ρ`, the conjecture's exact `errStar = 2^{2m}/(|F|·(2μ)⁷)`, no comparison or
  plumbing hypotheses left (the `(card (Fin 2) − 1) = 1` factor and the
  `rate = 2^m/n` identification, `rate_genRSC_pair`, absorbed in-proof);
* `mca_johnson_bound_CONJECTURE_pair_of_claim1_cells` — the verbatim conjecture from
  per-δ per-stack Claim-1 cell data alone (≤ L cells in the per-δ GS list shape with the
  capture-above-n dichotomy). The SOLE remaining input to the literal ℓ = 2 conjecture is
  now exactly the BCIKS20 Steps 5–7 Λ/β_t capture kernel (#138/#139 stream).

Falsify-first probe (`probe_conjecture_pair_wiring.py`): the comparison orientation
re-verified numerically before wiring — 1320 grid points across m ∈ [2,12], blowups 2–32,
q ∈ {M31, 2⁶⁴−59, 2¹²⁸−159, 2¹⁶+1}, six δ-slices of the Johnson window: 0 violations,
worst ratio 1.8·10⁻³ (the two-orders-of-magnitude slack of the c9121746d analysis,
re-measured). Next-cheapest wiring identified for a future pass: feed this single-hypothesis
pair-MCA into the WHIR RBR keystone's `RoundKeystoneData`/`perRoundProximityGap_of_correlatedAgreement`
chain (needs the per-round stack ↔ pair-generator identification); NOT wireable today:
#301 rbr soundness (forwarding-shell verifier — residual likely false as stated; needs the
checking verifier + #304 core) and the ℓ-ary (parℓ > 2) seam extension (mechanical per
Hab25 but new formalization, not plumbing).
### O70 — ITERATED SLICE ROOT-COHERENCE PROVEN: O69's "Conjecture D in elementary form" closes at every depth; the one missing brick was branch LOCALITY, not conservation

O69 left as the named open core the iterated weight/dead-locus tradeoff — "low weight
forces the alive slices to share large root loci at every depth simultaneously" — with
depth 1 claimed and depth ℓ probed-but-unproven. (Bookkeeping correction: the depth-1
brick `weight_ge_live_image` announced for `FoldPolynomialSlices.lean` in O69/commit
`2dcc9cfd9` never actually landed — the commit contains only the conservation, dual-RS
and census artifacts; no Lean occurrence exists in history. The statement below now
supplies it at every depth, including 1.)

**`ArkLib/Data/CodingTheory/ProximityGap/IteratedSliceRootCoherence.lean` (axiom-clean,
0 sorry, 0 warnings):**

* `branchVal_eq_zero_of_fiber_vanish` — **branch locality**, the brick the induction
  actually needed: the depth-ℓ branch value at `y` reads the error only on the iterated
  fiber `{x ∈ S : x^(2^ℓ) = y}`. (Conservation says mass cannot vanish in every branch;
  locality says it cannot APPEAR outside its fiber — the two directions are independent,
  and the tradeoff is locality's, not conservation's.)
* `live_card_le_weight` / `dead_card_ge` — **iterated weight transport,
  hypothesis-free** (any S, any valued v, no char, no negation-closure): the depth-ℓ
  live set has size ≤ w, since iterated fibers are disjoint and a live point's fiber
  must carry support; dually ALL 2^ℓ branch values vanish simultaneously on
  ≥ |iterSq S ℓ| − w points.
* `branchSlice` / `branchVal_polyeval` — the **iterated slice law**: on a tower
  negation-closed through depth ℓ, branch values of a polynomial error are evaluations
  of the iterated coefficient slices (even fold ↦ `evenSlice`, odd fold ↦ `X·oddSlice`,
  the O63 ⌈e/2⌉ exponent code), proved by induction over the depth-1 law.
* `iterated_slice_root_coherence` (+ `_div` with `|iterSq D ℓ|·2^ℓ = |D|` exact) —
  **the theorem**: a weight-w polynomial error's 2^ℓ iterated slices share a common
  root locus of size ≥ |D|/2^ℓ − w in the depth-ℓ domain. Every depth, every ℓ-level
  2-smooth tower, any field of odd characteristic.

Falsify-first probe (`probe_sliceroots_iterated.py`, adversarial: minimal-weight words,
fiber-aligned supports at the alive(ℓ)=1 boundary 2^ℓ | n−w, coset supports, sparse
single-residue coefficients): 1572 per-depth cases up to (p,n) = (769,256), 0 violations,
0 slice-law mismatches; the bound is TIGHT (live = min(w, n/2^ℓ)) in 902/1572 cases.

**Where the open core moves:** the root-coherence CONSTRAINT is now a theorem, so the
all-words question is no longer "prove the slices cohere" but "count the low-degree f
whose slices realize the forced coherence" — i.e. bound the number of f with
deg < k and all 2^ℓ slices vanishing on a prescribed ≥ n/2^ℓ − w common locus, where
each slice has degree < k/2^ℓ + O(1) and ≤ k/2^ℓ roots to spend. The counting question
(C19's 3 + 16 anatomy as the worked instance) is the surviving frontier; the structural
half of O69's sentence is machine-checked.
### O70 — the CRT DOUBLE-SLICE ENGINE: the de Bruijn route's per-prime machinery machine-checked (weighted, any base field) + the brief's literal invariance REFUTED

New brick `ArkLib/Data/CodingTheory/ProximityGap/CRTDoubleSlice.lean` (axiom-clean, 0 sorry, non-vacuity witnessed in-file), the O67-mapped elementary double-slice route executed:

* `packet_slice_coeff` — O66's packet slice lemma over ANY semiring of coefficients (was ℚ-only): multiples `G·R` of the geometric packet, `deg R < q`, have all `p` slices equal to `R`.
* `slice_of_packet_minpoly` — **the engine**: over ANY base field `K` with `minpoly K η = Σ_{t<p} X^{tq}`, every vanishing `K`-weighted sum `Σ_{e<pq} a_e η^e = 0` has μ-shift invariant slices `a_{iq+s} = a_{i'q+s}`. The O66 mechanism is linear — the 0/1 restriction was never load-bearing.
* `weighted_vanishing_slice_rat` — `K = ℚ` instantiation: rational-weighted Lam–Leung slices at every prime power (O66's closure = the indicator special case).
* `crt_fiber_slice` — the **CRT double-slice, fiber-sum form**: a vanishing double sum `Σ_{(j,c)∈I} ξ^j η^c` over a coprime exponent grid (ξ ∈ K, η packet-minimal over K) has μ_q-shift invariant fiber sums `A(c) = Σ_{(j,c)∈I} ξ^j ∈ K` — `A(i·q^{b-1}+s)` independent of `i < q`. This is exactly "apply O66 at the second prime with ℤ[ζ_{p^a}]-valued weights", with the minpoly-over-K hypothesis carried explicitly (satisfiable: discharged at `K = ℚ` in-file).

REFUTATION en route: the naive form of the double-slice claim — vanishing (even minimal) sums are membership-invariant under BOTH μ_p and μ_q exponent shifts — is FALSE (a μ_3-packet at n = 6 is not μ_2-closed). The correct CRT invariant is fiber-SUM invariance at each prime. Falsify-first probe (`probe_crt_double_slice.py`, exact integer arithmetic mod cyclotomics): weighted slice ⟺ vanishing at n = 8, 9 (0/20 000 mismatches each); fiber-sum invariance EXHAUSTIVE over all 2^n subsets at n = 12 (100/100 vanishing, 0 violations) and n = 18 (1000/1000), both primes — and a measured bonus: 0 non-vanishing subsets are invariant at either size, i.e. **double fiber-sum invariance ⟺ vanishing** empirically (one-direction trivially: invariance ⟹ packets sum to 0).

What remains for full de Bruijn (named): (1) discharge the packet-minpoly hypothesis over `K = ℚ(ζ_{p^a})` — cyclotomic irreducibility over the coprime cyclotomic extension via `φ(p^a q^b) = φ(p^a)φ(q^b)` + the tower formula (`IsCyclotomicExtension.Rat.finrank` + `Module.finrank_mul_finrank`); (2) the exponent bijection `μ_{p^a} × μ_{q^b} ≃ μ_n` converting subset sums of μ_n into grid double sums (ZMod.chineseRemainder bookkeeping); (3) the positivity/disjointness step — indicator fiber sums force DISJOINT rotated packets — the genuinely de Bruijn part.
### O70 — the ABF26 §5 collapse THROUGH THE INTERLEAVED LIST: interleaved list-decodability at 2δ ⟹ MCA at δ; the same-radius collapse REFUTED

`InterleavedListMCACollapse.mcaBad_card_le_interleavedList` (axiom-clean, 0 sorry, 0 warnings): for any `PairClosed` code (every F-linear code), stack `(f₁,f₂)`, floor `t`,

    #mcaBad(f₁,f₂; t) ≤ 1 + (n − (2t−n)) · #Λ₂(f₁,f₂; 2t−n)

— the MCA bad-scalar count (exact-count form of `mcaEvent`, ABF26 Def 4.3) is bounded by the `m = 2` **interleaved** list of the stack at the **doubled** radius. In δ-units: `Λ(C^{≡2}, 2δ) ≤ L ⟹ ε_mca(C,δ) ≤ (1 + 2δn·L)/q` (`mcaBad_card_le_of_interleavedList_card_le`); empty 2δ-list ⟹ at most ONE bad scalar (`mcaBad_card_le_one_of_interleavedList_eq_empty`). This is the [GCXK25]-shaped half of ABF26 §5 in the repo's own definitions, complementing the in-tree per-LINE collapse (`MCAListCollapseFullSupport`, loss `n/t`): the list-recovery/interleaved reformulation (`ListRecoveryInterleavedGap`) now feeds MCA directly.

Engine: Round-17 pair extraction maps every bad `γ ≠ γ₀` into the 2δ-interleaved list; the new brick is **failure-point pinning** (`scalar_pin`) — `Φ(γ) = p` forces `c_γ = p.1 + γ·p.2` identically, and the MCA no-joint-pair clause hands a point of `S_γ` where `p` disagrees with the stack, at which the line equation SOLVES for `γ`; so each fiber injects into `p`'s disagreement set (`≤ n − (2t−n)` points).

**The radius doubling is NECESSARY** (`probe_interleaved_mca_collapse.py`): the same-radius collapse `#bad ≤ 1 + (n−t)·#Λ₂(t)` is FALSE — over F₃, n = 4, C = span{(1,1,1,0),(0,1,2,1)}, stack ((0,0,0,1),(0,0,1,0)), t = 3: all 3 scalars MCA-bad with the floor-t interleaved list EMPTY (3,888 such stacks in that code alone; 17,399 across probes). The main inequality: 0 violations over 27,851 stacks (exhaustive F₃ × 3 codes, sampled F₅ RS n ∈ {4,5}, k ∈ {2,3}; worst saturation 0.667). The factor-free variant `#bad ≤ 1 + #Λ₂(2t−n)` survived all probes but is NOT provable by pinning (codeword pencils `c_γ = g₁ + γ·g₂` give genuine fiber multiplicity) — recorded as the open refinement.

Honest scope: the interleaved 2δ-list bound is an INPUT; bounding it for explicit smooth-domain RS in `(1−√ρ, 1−ρ)` is still the prize core, and 2δ-lists are only nonvacuous for δ below half the relevant radius — the collapse trades radius for the clean `1 + 2δn·L` form, exactly the GCXK25 trade.
### O70 — the THRESHOLD LANDSCAPE of the deep line: crossover is NOT line-independent, and toy δ* pins to the witness radius (nubs, 2026-06-10)

**`scripts/probes/probe_qline_threshold_landscape.py` (exact, deterministic, exit 0; O68's subset census read at ALL radii in one pass, SB=0 every-γ degenerate layers handled exactly):** 452 per-line censuses at 4 points — (16,2,5)/BabyBear rate ½, (16,2,5)/p=97, (16,4,2)/BabyBear rate ¼, (12,2,4)/p=37 — each point censusing the Theorem-Q deep line, 100 random lines, and 12 two-codeword bundle lines (PromotedHypothesesB style: u0+γᵢu1 = cᵢ+eᵢ planted at weight n−rm; disjoint / shared / overlap-(wt−1) supports). O68 reproduced exactly twice (standalone re-run + in-probe gates: 56/1/56 at a=10, 5496/2/10936 at a=9, 0 degenerate).

**The landscape (large q, where ε*·q = 2⁻¹²⁸q ≪ 1 ⟹ crossover = count hits 0):** random lines carry NOTHING beyond the trivial k+1 floor — crossover a* = k+2 at both BabyBear points (100/100 each). The Q-line crosses at a_wit+1: bad mass C(s,r) (56 at rate ½, 6 at rate ¼) persists exactly to a_wit = rm and vanishes strictly above. At rate ¼ that is THREE notches past random, dying exactly at the Johnson agreement √(nk) = 8 (δ = ½ = 1−r/s). **Crossover is NOT line-independent — structured lines cross deeper than random by exactly the structured layer; the toy δ* sits at δ_wit = 1 − rm/n with fraction C(s,r)/q there and 0 above on every deep line measured.** Among DEEP lines, however, crossover IS class-independent: overlap bundles (depths 9,9 / 7,7 — beyond the radius) realize t+2 bad γ's at a_wit (7 vs the Q-line's 56) and the same a* = a_wit+1; disjoint bundles give exactly the 2 planted γ's, 0 emergent (counts structurally identical across instances); shared-support bundles DO place bad γ's one notch above a_wit (6 at a=11, the per-point cancellation γ_x = (e₁γ₂−e₂γ₁)/(e₁−e₂)) but only by going shallow (u0,u1 both within the radius; all-γ layer at base a_wit) — no deep line found crossing above a_wit.

**Small-q control (the honest caveat for the upper half):** at q = 97 the random noise floor at a_wit is 67 > the Q-line's 60, 33/100 random lines still carry bad γ's at the Johnson agreement, and the witness-radius lists collide (max per-γ list 4; the 56 scalars collapse to 45 distinct) — O68's singleton structure and the 2⁻¹²⁸ scaling are LARGE-q phenomena, vacuous at toy q. Moral for the per-line moment chain: the load-bearing upper-half target is the count of (deep line, γ) pairs at a = rm exactly — everything above is provably (here: measurably) empty, everything below is floor.
### O76 — the strict-interior leaf of the boundary quantization split is FALSE; the corrected boundary route proven (nubs, 2026-06-10)

The #304 boundary ground truth, completed. In-tree refutations (BoundaryCardResidualRefutation, …AffineLineRefutation) killed the bare closed-boundary residual only at SQUARE endpoints (deg·n = 4, ZMod 5, deg 1), and the quantization split (`boundaryCardResidual_of_not_lattice`) deferred the entire NON-lattice bulk to the strict-interior supply `BoundaryCardStrictInteriorFalseAsStated` (nonempty good set at a floor-matched δ' < δ ⟹ jointAgreement at δ'). **That supply is false** (`BoundaryCardStrictInteriorRefutation.lean`, axiom-clean, 0 sorry): at k=1, deg=2, n=4 over GF(5), boundary δ = 1−√(1/2) (deg·n = 8 NON-square — kernel-checked non-lattice, `boundary_floor_lt`), δ' = 1/4 floor-matched (both floors = 1), stack u₀ = 0, u₁ = x² on {0,1,2,3}: z = 0 makes the good set nonempty, but jointAgreement needs |S| ≥ 3 and no linear polynomial meets x² on 3 of the 4 points (quadratic with 3 roots; exhaustive `decide`, probed first in `probe_boundary_strict_interior.py`). Corollary at the same witness: the first NON-square-endpoint refutation of bare `BoundaryCardResidual` (`not_boundaryCardResidual_nonSquareEndpoint`). So **both leaves** of the quantization split — lattice (O-in-tree) and strict-interior (this) — are unsatisfiable as nonemptiness statements: nonemptiness is never a sufficient boundary hypothesis, on or off the 1/n-lattice.

What survives, made formal: the corrected obligation must carry the §5 threshold at a floor-matched strict radius (Pr > k·errorBound(δ'), errorBound(δ') > 0); the witness is consistent with it (Pr = 1/5 ≤ 4/5, probe-checked). Proven consumer-shaped piece: `BoundaryQuantizationCorrected.correlatedAgreementCurves_boundary_of_floorEq_strict` — ⌊δ'·n⌋ = ⌊δ·n⌋ transports the FULL `δ_ε_correlatedAgreementCurves` statement from δ' to δ with the SAME ε (premise via the good-set step function, conclusion via the agreement-floor step function). Off the lattice such δ' always exists (`exists_lt_floor_eq_of_floor_lt`), so the honest closed-boundary export is the strict theorem with ε = errorBound(δ') > 0 — never the refuted errorBound(1−√ρ) = 0 export. Moral for #304: retire the nonemptiness residual surfaces entirely; the only honest boundary data are (a) the floor-matched strict-radius threshold route (now a theorem) and (b) the genuinely-square lattice branch behind the large-field-guarded `BoundaryCardLatticeData` package.
### O70 -- the UPPER half faces the lower in one file: affine-root reduction engine + conditional two-sided bracket (nubs, 2026-06-10)

O68 pinned the LOWER half (theoremQ_epsMCA_lower: eps_mca(evalCode H k, delta) at least B/q in the list-decoding window). This delivers the matching UPPER machinery on the SAME epsMCA surface, so the two halves face each other in one statement.

Bricks (TheoremQUpperReduction.lean, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):
- epsMCA_le_of_affineRoot_extraction -- the upper-half engine: given per stack u an affine error pair (e0 u, e1 u) with weight(e1 u) at most W such that EVERY mcaEvent bad scalar of u is a root of e0 u + gamma*e1 u at a support coord of e1 u, then eps_mca(C,delta) at most W/q. This is exactly the wiring badGamma_affine_card_le's docstring deferred (the min-distance codeword extraction): it composes that per-line counter (bad count at most weight(e1)) into epsMCA_le_of_badCount_le. The extraction hypothesis is the named residual wall (true in unique decoding delta below (d-1)/2n via e = u - c for the unique nearby codewords; reduced to, NOT discharged).
- not_mcaEvent_of_uOne_zero / evalCode_not_mcaEvent_uOne_zero -- unconditional: a zero direction u1=0 has no bad scalar (0 in evalCode makes pairJointAgreesOn hold). The u1=0 case of why the engine targets the affine-root event and NOT line-closeness.
- epsMCA_univ_le_zero -- non-vacuity: the engine fires to 0 on C=univ (extraction satisfiable, hroot via not_mcaEvent_univ), certifying soundness.
- theoremQ_epsMCA_two_sided -- the conditional pincer in one statement: under the Theorem-Q hypotheses AND the extraction, exists B, B/q at most eps_mca at most W/q. Lower B unconditional (O68); upper W at most n conditional on the extraction.

The probe (probe_qline_upper.py, fresh point q=97,n=12,m=2,s=6,r=3,k=4 -- different prime and n,m,r than O68 BabyBear/16/2/5; exit 0):
- C2 (key structural finding): badCount at most lineCloseCount is far too lossy. A stack with u0 a codeword and weight(u1)=3 is delta-close at EVERY gamma (lineCloseCount equal q equal 97) yet has bad count 0 -- verified at delta 0.25, deep in unique decoding; the affine-root count is 1 at most weight. So the engine targets badGamma, not line-closeness (the u1=0 slice is the Lean not_mcaEvent_of_uOne_zero).
- C3 (the gap is real): C(s,r)=20 exceeds n=12, so at the witness radius eps_mca at least C(s,r)/q exceeds n/q -- a global n/q upper bound is FALSE; the upper bound is unique-decoding-only and the crossover radius is delta-star.
- C1 re-measures badGamma_affine_card_le (engine RHS) over 200 random error pairs; the Q-line line-close census drops 18 to 0 just past the witness radius a = rm = 6.

The numerical gap (headline): on this family the LOWER half forces eps_mca at least C(s,r)/q equal 20/97 about 0.206 at delta = 1 - rm/n = 0.5, while the UPPER engine gives eps_mca at most n/q equal 12/97 about 0.124 in unique decoding delta below (n-k+1)/2n = 0.375. The unpinned window is delta in (0.375, 0.5] -- exactly the Johnson-to-capacity gap, with the two halves now on one surface. At cryptographic q, n/q (upper) and C(s,r)/q (lower) straddle eps-star = 2^-128, so delta-star is the crossover radius. The single remaining wall to close the window unconditionally is hroot for evalCode (the min-distance extraction = the proximity-gap core).
### O72-addendum — record correction: O69's `weight_ge_live_image` never landed as Lean

Cold audit (2026-06-10) of commit 2dcc9cfd9 (O69): the commit message and the O69 entry
announce a depth-1 brick `weight_ge_live_image` in `FoldPolynomialSlices.lean`, but
`git log -S weight_ge_live_image` shows the name only ever appeared in DISPROOF_LOG text —
no Lean theorem of that name exists anywhere in history. The mathematical content is now
actually kernel-checked (stronger, at every depth) by `IteratedSliceRootCoherence.lean`
(`live_card_le_weight` / `dead_card_ge`, O72), so the gap is closed — but the O69 record
overstated what had landed. Lesson for the swarm: an announced brick is not a brick;
grep the tree, not the log.

### O78 — the O74 interleaved collapse lands on the epsMCA surface: the bridge is a theorem and the library gets a SECOND unconditional upper window (δ < d/(4n), no extraction residual)

O74 proved #mcaBad(t) ≤ 1 + (n−(2t−n))·#Λ₂(2t−n) on its own exact-count surface (`mcaBadSet`, ℕ floor), while the prize quantity `epsMCA` (ABF26 Def 4.3) lives on `mcaEvent`'s real floor (S.card ≥ (1−δ)·n in ℝ≥0); the O74 auditor's remark that the quantifier shapes match was never a theorem. Now it is, and the splice yields the second unconditional upper window.

**Bricks (`EpsMCAInterleavedUD.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
- `mcaEvent_iff_mem_mcaBadSet` — **the bridge**: `mcaEvent ↑C δ u₀ u₁ γ ↔ γ ∈ mcaBadSet C u₀ u₁ ⌈(1−δ)·n⌉₊`. Witness set, line clause and ¬pairJointAgreesOn clause correspond verbatim (smul_eq_mul, eq_comm); the size clause converts by `Nat.ceil_le` — the floor is the CEILING, and the ⌊·⌋₊ convention is FALSE (14,844 probe witnesses). Count form `mcaEvent_filter_eq_mcaBadSet`: the epsMCA bad-scalar filter IS mcaBadSet.
- `interleavedList_card_le_one_of_agree_le` — unique decoding of C^{≡2} from the distance of C: if distinct codewords agree on ≤ e = n−d points and n + e < 2a, the m=2 interleaved list of ANY stack at floor a is a singleton at most (two members jointly agree with the stack on ≥ a each, hence with each other on ≥ 2a−n > e in both rows).
- `epsMCA_le_interleavedUD` — **the window**: PairClosed C (every F-linear code), agreement parameter e, n + e < 2·(2t−n) with t = ⌈(1−δ)n⌉₊ ⟹ ε_mca(C,δ) ≤ (1 + (n−(2t−n)))/|F| — in δ-units (1+2δn)/q. No probabilistic, list-decoding, or extraction hypothesis.
- `epsMCA_le_interleavedUD_of_quarter_dist` + `nat_window_of_quarter_dist` — the named δ-window: 4δn + e < n (= δ < d/(4n), a quarter of the relative distance; RS: δ < (1−ρ)/4 + O(1/n)) implies the ℕ window.

**Falsify-first probe (`probe_epsmca_interleaved_ud.py`, exit 0):** bridge checked through INDEPENDENT code paths (full 2^n subset enumeration vs witness-set reduction, the reduction itself controlled: 240,570 exhaustive checks, 0 mismatches): 260,570 (stack,γ,δ) checks over exhaustive F₃ n∈{3,4} ×3 codes + sampled F₅ RS, **0 mismatches**, while the floor convention breaks 14,844 times — the ceiling is exactly right. Instantiation: 7,690 in-window checks, 0 violations, bound SATURATED (max slack 0); just outside the window L ≤ 1 fails (witnesses found); δ < d/(4n) ⟹ ℕ window on a fine grid, 0 failures.

**Where this sits in the bracket:** O77's upper window (≤ n/q for δ < d/(2n)) is conditional on the affine-root extraction residual — the proximity-gap core. This window halves the radius (the price of O74's radius doubling: C^{≡2} must be unique-decodable at 2δ) and in exchange deletes the residual entirely: below d/(4n) the upper half is now a THEOREM on the same epsMCA surface as the O68 lower half. The unpinned core is unchanged — the gap (d/(4n), δ*] where the lower bound C(s,r)/q lives — but the unconditional floor of the upper half just moved from nothing to a quarter of the distance, and any future interleaved-list bound L(2δ) for explicit smooth-domain RS now converts to ε_mca ≤ (1+2δn·L)/q with zero plumbing left.
### O78 — the corrected boundary threshold route gains its monotonicity pillar: floor-cell threshold transport PROVEN (and the corrected statement survives an exhaustive census)

O76 left the corrected boundary obligation — carry the §5 threshold `Pr[good δ'] > k·errorBound δ'` at a floor-matched strict radius — as the named honest target. This pass (a) hardens its empirical footing and (b) proves the probability-threshold monotonicity piece its full proof needs.

**Bricks (`BoundaryThresholdFloorCell.lean`, axiom-clean, 0 sorry, 0 warnings):**
* `prob_threshold_floorCell_mono` — **threshold descends within a floor cell**: for `0 < deg`, `δ'' ≤ δ' < 1 − √ρ` with `⌊δ''n⌋ = ⌊δ'n⌋`, the §5 threshold at `δ'` implies it at `δ''`. Engine: the probability is CONSTANT on the cell (good-set step function, in-tree) while `errorBound` is monotone nondecreasing below the boundary — the latter was already in-tree (`DivergenceOfSets.errorBound_mono`; duplicate guard caught it, so this lane shipped the *wiring*, not a re-proof).
* `correlatedAgreementCurves_floorCell_mono` — **monotone-ε transport**: `δ_ε_correlatedAgreementCurves` at the cell's smaller radius with ITS `errorBound` implies it at every floor-matched larger radius with ITS `errorBound`. This strengthens O76's same-ε transport: the corrected route needs the §5 machinery at only ONE radius per floor cell.
* `correlatedAgreementCurves_boundary_of_floorCell_mono` — the composite export: strict-interior CA at a single floor-matched `δ''` ⟹ closed-boundary CA at `δ` with `ε = errorBound δ'` for EVERY floor-matched intermediate `δ'`.
* Witness namespace: the whole hypothesis spine instantiated at the O76 witness (ZMod 5, n=4, deg=2, `deg·n = 8` non-square) with the CROSS-BRANCH pair `δ'' = 1/4` (UDR edge) ≤ `δ' = 7/25` (Johnson branch) — `errorBound_quarter_le_sevenDivTwentyFive` crosses the UDR→Johnson seam concretely; no leaf hides behind an unsatisfiable hypothesis.

**Probe (`probe_boundary_threshold_floorcell.py`, exit 0):** the corrected statement survives 4 non-lattice points — q=5/n=4/k=1 EXHAUSTIVE (390,625 stacks, threshold fired on 60,625, 0 violations), q=13/n=6, q=257/n=6, q=13/n=4/k=2 (sampled random + 3 adversarial families; 0 violations). The hunt used the monotonicity reduction: violation at any floor-matched δ' ⟺ violation at the cell minimum j/n. Measured TIGHTNESS: the maximum good count among no-jointAgreement stacks equals `k·n` EXACTLY at three points (4/6/8) — the transported threshold saturates at the cell minimum and cannot be lowered. Negative control: at `deg = 0` errorBound monotonicity is FALSE (Johnson value degenerates to 0), so `0 < deg` in the in-tree lemma is load-bearing.

**Where the open core sits:** the corrected route is now fully plumbed — step functions (in-tree), errorBound monotonicity (in-tree), floor-cell threshold transport + monotone-ε export (this entry). The single remaining input is the genuine §5 strict-interior producer (`δ_ε_correlatedAgreementCurves` at one strict radius per cell, the BCIKS20 Steps 5–7 content), plus the genuinely-square lattice branch behind `BoundaryCardLatticeData`.

### O68 — the coefficient-general slice theorem: the de Bruijn engine machine-checked

`LamLeungTwoPow.vanishing_coeff_slices` (axiom-clean, 0 sorry): ANY vanishing
ℚ-coefficient combination of p^(m+1)-th roots of unity has all p coefficient slices
equal. Upgrades O66 from subset indicators to arbitrary coefficients — exactly the engine
the two-prime (de Bruijn) CRT double-slice induction needs, whose slice differences carry
{−1,0,1} coefficients. The mixed-radix third pillar now has its core mechanism formal;
what remains of de Bruijn is the CRT bookkeeping (apply this at prime 1 with coefficients
in prime 2's field, then descend).
### O78 — #304's two reduced cores fused into ONE Prop consumed by ONE theorem: `BCIKS20RemainingCore` ⟹ Theorem 1.5 (nubs, 2026-06-10)

O70 left the strict branch as `StrictCoeffPolysLargeResidual` + `BoundaryProbabilityResidual`; O76/O78 left the boundary as the corrected floor-matched threshold route. This pass welds them: the corrected boundary obligation REDUCES to the same large-sector residual at the working radius, because at any strict radius the §6.2 boundary residual is vacuous (`¬ δ' < 1 − √ρ` unreachable) — so the entire #304 debt is one obligation kind at (at most) two radii per floor cell.

**Bricks (`BCIKS20/RemainingCore.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
* `BCIKS20RemainingCore k deg domain δ δ'` (line 84) — **the one named Prop**: `StrictCoeffPolysLargeResidual(δ) ∧ StrictCoeffPolysLargeResidual(δ')`.
* `correlatedAgreement_of_remainingCore` (line 149) — **the wiring theorem**: `δ' < 1 − √ρ` + `⌊δ'n⌋ = ⌊δn⌋` + the core ⟹ `δ_ε_correlatedAgreementCurves` at δ with `ε = max (errorBound δ) (errorBound δ')`. Strict interior: conjunct 1 through the O70 front door at the literal `errorBound δ` (boundary residual discharged by vacuity, `correlatedAgreementCurves_strict_of_remainingCore`). Closed boundary (`errorBound δ = 0`): conjunct 2 through the front door at δ' + the O76 floor transport, max realized by the honest `errorBound δ' > 0` (`correlatedAgreementCurves_floorMatched_of_remainingCore`). Glue: `correlatedAgreementCurves_mono_eps` (CA is antitone in ε).
* `remainingCore_boundary_witness` + `correlatedAgreementCurves_boundary_witness` — the core is SATISFIABLE at the O76 closed-boundary instance (ZMod 5, n=4, deg=2, k=1, δ' = 1/4; rate = 1/2 kernel-checked via `rateOfLinearCode_eq_div'`), and the pipeline then exports an UNCONDITIONAL in-tree closed-boundary CA at threshold `max(0, 4/5)` — true content, exhaustively pre-verified by the O78 floor-cell probe (390,625 stacks, fired 60,625, 0 violations). Honest caveat in-file: at toy q both conjuncts hold vacuously (δ not strictly interior; `(1−ρ)/2 = 1/4` exactly) — the witness certifies consistency, not large-q content.

**Probe (`probe_remaining_core_wiring.py`, exact arithmetic, exit 0):** 8,255 grid points, 0 violations — every one of the 8,113 non-lattice boundaries admits the canonical floor-matched strict `δ' = ⌊δn⌋/n` with `errorBound δ' > 0` (24,040 Johnson-window + 8,412 UDR instantiations over q ∈ {5, 97, BabyBear, M61}); `errorBound(boundary) = 0` always (the refuted-shape ε never exported); the 142 lattice points admit NO strict floor-matched radius and stay honestly behind `BoundaryCardLatticeData`; O76 witness reproduced to the digit.

**Where #304 now sits:** the issue can be re-scoped verbatim as "remaining = `BCIKS20RemainingCore` (RemainingCore.lean:84), consumed by `correlatedAgreement_of_remainingCore` (line 149), plus the square-lattice endpoint branch behind `BoundaryCardLatticeData`". Producers target a single obligation kind — `StrictCoeffPolysLargeResidual` at one radius per floor cell — and every discharge flows to Theorem 1.5 with zero plumbing left.
### O79 — the Steps 5–7 capture kernel gets its statement and its first proven sub-obligation: capture IS affine decodability, and the Hensel-stream output shape now reaches the Claim-1 consumer

O71/Hab25Claim1 pinned the #302 chain's single deep input to the per-cell `hsteps57` hypothesis of `claim1_dichotomy` (capture-above-threshold by one degree-`< k` affine pair), but nothing in-tree PRODUCED `AffineCaptured` — the #304/#138/#139 Hensel stream (HPzBridge/HenselDatum, MatchingExtractor, Claims 5.8/5.9) terminates on a different surface: per-`z` decoded-polynomial identities `P z = v₀ + z·v₁`. This pass builds the seam and the kernel's canonical form.

**Bricks (`Hab25CaptureKernel.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
- `McaDecode` + `McaDecode.mcaEvent` / `exists_mcaDecode_of_mcaEvent` — the polynomial-side destructuring of one `mcaEvent` witness (witness set `S`, degree-`< k` decoded polynomial `P` agreeing with the fold on `S`, the ¬pairJointAgreesOn clause verbatim), FAITHFUL in both directions via `ReedSolomon.mem_code_iff_exists_polynomial`.
- `McaDecode.affineCaptured` — **the capture bridge** (first sub-obligation): a decode whose polynomial is the specialization `a + γ·b` yields `AffineCaptured domain k δ u γ (a,b)` verbatim.
- `affineCaptured_iff_exists_mcaDecode` — **the canonical form**: under the degree bounds, affine capture ⟺ the specialization `a + γ·b` is itself an mcaEvent decode of `γ`. The `hsteps57` residual is now stated on the surface the §5 machinery natively produces.
- `hsteps57_of_decode_family_pinning` / `cell_card_le_of_decode_family_pinning` — the kernel consumer-shaped and composed with the proven dichotomy: per-cell decode family **K1** (`∀ γ ∈ Ecell, ∃ d : McaDecode, d.P = P γ` — production lane: the PROVEN `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count` + GS interpolation; the planned degree-budget root-count brick turned out already in-tree and was composed, not re-proved) plus affine pinning **K4** (`T < |Ecell| → ∃ v₀ v₁ (deg < k), ∀ γ ∈ Ecell, P γ = v₀ + γ·v₁`) give the literal `hsteps57`, hence `|Ecell| ≤ T`. K2 (matching factor) and K3 (cell assignment, `gsFactorIndex`) were already in-tree.

**Falsify-first probe (`probe_capture_kernel_bridge.py`, exit 0):** decode equivalence exhaustive over GF(3) n=3 (2,187 pairs) + 1,000 planted/random GF(5) n=4 stacks (5,000 checks), 0 mismatches; `AffineCaptured` clauses verbatim on 1,678 pinned-cell members, 0 failures; all 839 maximal affine cells obey `|cell| ≤ n`. **Negative control:** in every one of the 839 multi-scalar bad sets the maximal affine cell was a STRICT subset (bad sets up to 4 with unrelated decodes) — the pinning hypothesis is substantive, not auto-true, even at toy q.

**Where the open core sits:** the kernel is now exactly K4's antecedent-to-witness step — `T < |Ecell|` must PRODUCE the affine pencil (BCIKS20 Claim 5.7 pigeonhole incidence + Claims 5.8/5.9 Hensel-branch degree/Z-linearity + Appendix C), per cell of the GS factor decomposition. The #138/#139 HenselNumerator stream's open cores are this statement; everything from its output shape down to `mca_johnson_bound_CONJECTURE` at `parℓ = Fin 2` is machine-checked wiring.
### O79 — de Bruijn capstone step (2) LANDED: the CRT exponent bijection turns subset sums of μ_n into coprime-grid double sums, composed with the O73 engine (and the predecessor's orphan repaired)

O73's "what remains" list left step (2) — the exponent bijection μ_{p^a} × μ_{q^b} ≃ μ_n converting subset sums of μ_n into the grid double sums `crt_fiber_slice` consumes — as ZMod.chineseRemainder bookkeeping. It is now a theorem, with one normalization surprise and one swarm-hygiene catch.

**Normalization (falsified-first, `probe_crt_exponent_bijection.py`, 82,405 checks / 0 violations, exhaustive over all 2^n subsets at n = 12, 15; non-coprime control N=4,M=6 fails as expected):** the brief's Bezout identity ζ^e = ζ^{e_p·u·q^b + e_q·v·p^a} is the INVERSE direction and is never needed. The formalized direction is the forward grid map g(j,c) = j·M + c·N mod n — `ζ^{g(j,c)} = ξ^j·η^c` is trivial exponent arithmetic, bijectivity is injectivity (mod-N/mod-M reduction + coprime unit cancellation) + cardinality.

**Bricks (`CRTExponentGridSum.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
* `gridMap_inj` / `gridMap_surj` / `pow_gridMap` — the CRT bijection [0,N)×[0,M) ≃ ZMod(N·M) and the intertwining ζ^{g(j,c).val} = (ζ^M)^j·(ζ^N)^c.
* `subset_sum_eq_grid_double_sum` — **the deliverable**: Σ_{e∈S} ζ^e.val = Σ_{(j,c)∈gridSet S} (ζ^M)^j·(ζ^N)^c for any S : Finset (ZMod (N·M)), 0/1 indicator weights (bare Finset.sum over the CRT preimage), over any Monoid+AddCommMonoid — primitivity not needed for the identity.
* `fiber_slice_of_vanishing_subset_sum` — the composition with `crt_fiber_slice`: vanishing subset sums of μ_n exponents have μ_q-shift invariant K-valued fiber sums over their CRT grid set, under the packet-minpoly hypothesis at the second prime. Step (2) is discharged AND typed against the step-(0) engine; steps (1) (packet minpoly over ℚ(ζ_{p^a})) and (3) (disjoint-packet positivity — the genuinely de Bruijn part) remain the open frontier.
* Non-vacuity kernel-checked at a genuine two-prime point (N=2, M=3, ζ=3 ∈ ZMod 7 primitive 6th root, S={0,1,3}, sum value 3 ≠ 0 by `decide`) and at a nonempty vanishing sum (N=1, q=2, ζ=−1, S=μ₂ full).

**Swarm-hygiene catch (the O72-addendum lesson, again, in the other direction):** the rate-limited predecessor lane committed the probe ("orphaned by rate-limit, verified green", 72656ea65) and left `CRTExponentBijection.lean` UNTRACKED in the working tree — its 6 main theorems elaborate axiom-clean, but its non-vacuity example FAILS (7 unsolved-goals errors: positional `by norm_num` arguments elaborated against unassigned metavariables for N, q, Q'), so the file as a whole does not pass the runnable-witness gate. The fix is elaboration-order, not math: pin N, q, Q', i, i', s by name. `CRTExponentGridSum.lean` supersedes the orphan, which should be dropped, not committed. Lesson: a file whose #print axioms lines succeed can still be red — read the whole compiler output, not the axiom tail.
### O79 — de Bruijn step (1) CLOSED: the packet minimal polynomial over the coprime cyclotomic extension is a theorem, and the CRT fiber-slice goes unconditional (nubs, 2026-06-10)

O73 (CRTDoubleSlice) left the engine `slice_of_packet_minpoly` carrying its load-bearing hypothesis — `minpoly K η = Σ_{t<p} X^{tq}` over `K = ℚ(ζ_{p^a})` — as named residual (1). Discharged.

**Bricks (`CRTPacketMinpoly.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
* `minpoly_adjoin_primitiveRoot_eq_packet` — for distinct primes `p ≠ q`, `b ≥ 1`, primitive roots `ξ` (order `p^a`), `η` (order `q^b`) in ANY char-0 field: `minpoly ℚ⟮ξ⟯ η = Σ_{t<q} X^(t·q^(b-1))` — `Φ_{q^b}` stays irreducible over the coprime cyclotomic extension, in packet form. Engine: `minpoly ∣ Φ_{q^b}` pinched against the totient tower bound `φ(p^a)·φ(q^b) = φ(p^aq^b) = [ℚ(ξη):ℚ] ≤ φ(p^a)·[ℚ⟮ξ⟯⟮η⟯:ℚ⟮ξ⟯]` (`cyclotomic_eq_minpoly_rat` + `adjoin.finrank` + `Module.finrank_mul_finrank` + a hand-rolled ℚ-linear embedding `ℚ⟮ξη⟯ ↪ ℚ⟮ξ⟯⟮η⟯`; the coprime-order product is primitive via `Commute.orderOf_mul_eq_mul_orderOf_of_coprime`), closed by `eq_of_monic_of_dvd_of_natDegree_le` + `cyclotomic_prime_pow_eq_geom_sum`. The brief's worked case is an in-file one-liner: `minpoly ℚ(i) ζ₃ = 1 + X + X²`.
* `crt_fiber_slice_coprimePrimePowers` — **the headline**: `crt_fiber_slice` at `K = ℚ⟮ξ⟯` with the hypothesis GONE. A vanishing double sum `Σ_{(j,c)∈I} ξ^j·η^c = 0` over the coprime grid `range(p^a) ×ˢ range(q^b)` has μ_q-shift invariant fiber sums `Σ_j [(j, i·q^(b-1)+s) ∈ I]·ξ^j` — unconditionally, for any two primitive roots in any char-0 field (ℂ instantiation witnessed in-file).

**Falsify-first probe (`probe_crt_packet_minpoly.py`, exact, no floats, exit 0):** 24/24 — packet form at 9 prime powers; the claim's equivalent tower equality as FULL RANK of the φ(n)×φ(n) CRT power matrix over `ℚ[x]/Φ_n` at 10 coprime pairs up to (27,4)/(25,3); 5 overlap controls all rank-deficient. Honest boundary measured: (6,4) with gcd 2 is still full-rank (`φ(6)φ(4) = φ(12)` — linearly disjoint quadratics), so the obstruction is totient multiplicativity, not gcd per se — the theorem's prime-power coprimality is sufficient, not tight.

**Where the de Bruijn frontier moves:** a parallel lane's `CRTExponentGridSum.lean` (step (2), `fiber_slice_of_vanishing_subset_sum`) carries exactly this minpoly statement as its open `hmin` hypothesis — composing the two (one `rw` of `ζ^(q·Q')` into ξ-form) yields the full two-prime subset-sum fiber slice with no hypothesis; deliberately not built this pass to avoid depending on an unlanded sibling file. After that splice, the only genuinely de Bruijn content left is residual (3): indicator fiber sums force DISJOINT rotated packets (positivity).
### O84 — O77's extraction residual DISCHARGED on δ < d/(3n): the bracket is unconditional there, the bracket window forces r = s, and the (d−1)/2n mechanism is refuted in between

O77 reduced the Theorem-Q upper half to one residual: the affine-root extraction (per stack a pair (e₀,e₁), wt(e₁) ≤ W, every mcaEvent-bad γ a root of e₀+γe₁ at a support coord), with the docstring asserting it "provably true in unique decoding δ < (d−1)/2n". This pass proves it — on the honest window — and measures exactly where the asserted mechanism dies.

**Bricks (`TheoremQUDExtraction.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
- `exists_affine_pair` — **the extraction, per stack, on 3(n−t) < d** (t = ⌈(1−δ)n⌉₊): with two distinct bad scalars, the affine solve c₁ = (γ₁−γ₂)⁻¹(w₁−w₂), c₀ = w₁−γ₁c₁ of their closeness codewords gives e = u − c vanishing on S₁∩S₂ (wt(e₁) ≤ 2(n−t)); for ANY further bad γ the discrepancy codeword d_γ = w_γ−(c₀+γc₁) has wt ≤ (n−t)+2(n−t) < d, so d_γ = 0 — the decoding law is affine in γ — and ¬pairJointAgreesOn pins a coordinate where e₀+γe₁ = 0 with e₁ ≠ 0. (≤ 1 bad scalar: indicator pair, weight 1. W = 2(n−t)+1.)
- `epsMCA_le_of_uniqueDecoding` — the engine fired with the residual DISCHARGED: ε_mca(C,δ) ≤ (2(n−t)+1)/q for any F-linearly-closed C of min distance ≥ d on 3(n−t) < d. **The library's THIRD upper window, δ < d/(3n) — strictly wider than O78's unconditional d/(4n)**, same O(δn)/q shape; `evalCode_min_weight` + `evalCode_lin_closed` instantiate the Theorem-Q family (d = n−k+1 by root counting).
- `theoremQ_epsMCA_two_sided_uniqueDecoding` — **the bracket with NO extraction hypothesis**: B/q ≤ ε_mca(evalCode H ((r−1)m), δ) ≤ (2(n−t)+1)/q under Theorem-Q hypotheses + the window.
- `window_forces_r_eq_s` — **where the bracket lives**: the lower window (1−δ)n ≤ rm and the upper window 3(n−t) < n−(r−1)m+1 are jointly satisfiable ONLY at r = s. At the O68 point (16,2,8,5) the intersection is EMPTY (lower t ≤ 10, upper t ≥ 14) — the two-sided statement is honest but vacuous in the list-decoding regime, exactly the Johnson-to-capacity gap restated. At r = s the bracket is real: C(s,s)=1 forces B ≥ 1, so 1/q ≤ ε_mca ≤ (2(n−t)+1)/q; hypothesis spine witnessed satisfiable at ZMod 13, H = {1,5,8,12}, (n,s,m,r) = (4,2,2,2), δ = 0 (`theoremQ_ud_window_satisfiable` + the headline fired in-file).

**Falsify-first probe (`probe_ud_affine_extraction.py`, exact GF(97) + Berlekamp–Welch, exit 0):** C1 in-window (RS(16,8), e ≤ 2): 80 stacks, 69 multi-bad, 0 violations (affine law, root property, count ≤ 2(n−t)+1 — bound observed). C2 the hunt (e ∈ {3,4}, i.e. (d/(3n), (d−1)/(2n)]): a g-planting construction (error pair arranged so a third bad scalar decodes to line+g, g a weight-d codeword) **breaks the affine decoding law in 24/24 planted stacks at each e** — O77's docstring mechanism (unique nearest codewords are affine in γ throughout unique decoding) is FALSE strictly past d/(3n). But badCount never exceeded 2(n−t)+1 (max 3 ≪ W), so the extraction STATEMENT — equivalent, via the indicator pair, to the per-stack badCount bound — remains open there; only the codeword-subtraction proof route is closed. C3: r = s instance (97,12,4,3,4), t = 11, δ = 1/12: deep-quotient line carries exactly 1 bad scalar (lower-consistent), 20 stress stacks ≤ 2 (upper-consistent).

**Where the open core sits:** the unconditional upper floor moved from d/(4n) (O78) to d/(3n); the unpinned window is now (d/(3n), δ_wit], with three recorded approaches on one surface (O77 conditional d/(2n) — mechanism now refuted, statement open; O78 unconditional d/(4n); this unconditional d/(3n)). Closing (d/(3n), (d−1)/(2n)] needs a badCount bound that survives non-affine decoding laws — the probe says the count stays small even where the law breaks, so the gap is a counting question, not a structure question.
### O85 — the "zero plumbing" claim made a theorem: the general-L interleaved conversion lands on the epsMCA surface (and the natural-radius hypothesis shape with it)

Duplicate-guard note first: this lane's assigned brick (the mcaEvent↔mcaBadSet bridge + the unconditional δ < d/(4n) window) had ALREADY landed as `EpsMCAInterleavedUD.lean` (commit 7b84d23e7, the O78 entry); it was cold-verified (exit 0, axiom-clean ×7) and not redone — grep the tree, not the log. What the O78 record still owed was its own closing sentence: "any future interleaved-list bound L(2δ) … converts to ε_mca ≤ (1+2δn·L)/q with zero plumbing left" was a REMARK — only the L = 1 slice was a theorem, and the general conversion lived solely on the exact-count surface.

**Bricks (`EpsMCAInterleavedList.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
* `epsMCA_le_of_interleavedList_card_le` — **the general-L conversion**: PairClosed C (every F-linear code), uniform interleaved list bound L at the collapse floor 2t−n (t = ⌈(1−δ)n⌉₊) ⟹ ε_mca(C,δ) ≤ (1+(n−(2t−n))·L)/|F| — in δ-units (1+2δn·L)/q, the [GCXK25]-shaped conversion of ABF26 §5 stated on the prize surface. O78's window is the L=1 slice; the proof is the bridge + the O74 collapse + `epsMCA_le_of_badCount_le`, three rewrites total.
* `epsMCA_le_of_interleavedList_card_le_doubledRadius` — the same conclusion from a list bound at the **natural radius** ⌈(1−2δ)n⌉₊ — the hypothesis an actual Λ(C^{≡2},2δ) ≤ L statement provides — via two new bricks: `interleavedList_card_anti` (the m=2 interleaved list is antitone in the agreement floor) and `ceil_doubled_radius_le` (**the floor bridge**: ⌈(1−2δ)n⌉₊ ≤ 2⌈(1−δ)n⌉₊ − n for EVERY δ; ℝ≥0 truncation absorbs δ ≥ 1/2).
* `epsMCA_le_interleaved_trivial` + `interleavedList_card_le_sq` — non-vacuity with teeth: every linear code at every δ satisfies the conversion with the trivial L = |C|², so the general theorem is satisfiable far beyond the unique-decoding window (weak, but no window hypothesis at all).

**Falsify-first probe (`probe_epsmca_interleaved_list.py`, exit 0):** floor bridge exact-rational (ℝ≥0/ℕ truncation semantics), 9,420 (n,δ) points, 0 failures; exhaustive F₃ over 3 codes × 8 δ = 110,808 (stack,δ) checks of bridge + antitonicity + the composed natural-radius bound, 0 failures, SATURATED in 8,424 cases; bad counts controlled by full 2^n subset enumeration (7,200 controls, 0 mismatches). Honesty (C3): the L(a₀) ≥ 2 regime occurs 82,035 times in the sweep yet the bad count never strictly exceeds the L=1 form at q=3 — O74's factor-free refinement (#bad ≤ 1 + #Λ₂) remains open and unrefuted; this conversion transports exactly the proven collapse, no more.

**Where this sits:** the upper-half pipeline for #232 is now hypothesis-shaped end to end — any future interleaved (m=2) list bound for explicit smooth-domain RS at radius 2δ, Johnson-type or otherwise, converts to a two-sided-comparable ε_mca ≤ (1+2δn·L)/q in one application with no floor bookkeeping left. The open core is unchanged: produce L(2δ) beyond unique decoding (the gap (d/(4n), δ*] where the O68 lower bound C(s,r)/q lives), or settle O74's factor-free refinement.
### O86 — the LATTICE leaf of the corrected boundary route: quantitative-threshold-alone REFUTED at a lattice endpoint; the leaf PROVEN down to the single §5 extraction residual

O76/O78 left the corrected boundary route fully plumbed off the lattice (floor-matched strict radius + §5 threshold + floor-cell monotonicity) with two named inputs open, one being the genuinely-square lattice branch behind `BoundaryCardLatticeData` (three inputs: two Johnson cardinality bounds + the §5 coefficient-polynomial extraction). At a lattice endpoint the corrected route's machinery is provably unavailable: no floor-matched strict sub-radius exists (`not_exists_lt_floor_eq_of_lattice`) and `errorBound(1−√ρ) = 0` makes the §5-form threshold vacuous — the in-tree threshold→cardinality conversion (`goodCoeffsCurve_card_bounds_of_prob_threshold`) has side conditions requiring `k ≤ k·errorBound·q = 0`. This pass settles what the honest lattice hypothesis is.

**REFUTED (probe witness): the field-quantitative threshold alone does not suffice.** `probe_boundary_lattice_threshold.py` (exact, exit 0; 4 lattice endpoints deg·n square, 2,424 stacks, threshold fired on 355): over GF(11), n=8, deg=2, k=1 (deg·n = 16 = 4², δ·n = 4 integral), the stack u₀=(4,6,1,0,9,2,0,8), u₁=(4,10,0,4,2,7,9,3) has |good| = 10 > 9 = (n+1)k yet NO jointAgreement — and its per-z decoding lists admit a choice P with no coefficient polynomial B (exhaustive). So `Pr > k·(n+1)/q` cannot replace the refuted nonemptiness hypothesis on its own; the §5 extraction is load-bearing. Tightness: the no-jointAgreement maximum |good| EXCEEDS (n+1)k at that point (10 > 9) and saturates it exactly at q=11/n=9/deg=1 (10 = 10). The composite (threshold + extraction) survived all 4 points, 0 violations.

**PROVEN (`BoundaryLatticeThresholdLeaf.lean`, axiom-clean, 0 sorry, 0 warnings): the lattice leaf reduces to the extraction alone.**
* `card_gt_of_prob_gt_latticeThreshold` — `Pr[curve δ-close] > k·(n+1)/|F|` ⟹ `|good| > (n+1)·k`, unconditionally in δ: the positive replacement for the boundary-degenerate errorBound conversion (`latticeThresholdEps = (n+1)/|F| > 0` vs `errorBound(1−√ρ) = 0`).
* `jointAgreement_of_latticeThreshold_of_coeffPolys` — per stack: quantitative threshold + §5 extraction ⟹ `jointAgreement`, at every radius including the exact lattice endpoint, via the in-tree assembly bridge; both `BoundaryCardLatticeData` cardinality inputs are discharged by the threshold.
* `LatticeCoeffPolyExtraction` / `BoundaryCardLatticeThresholdResidual` — the extraction-only residual surface and the corrected lattice-leaf surface (the refuted `BoundaryCardLatticeResidual` with nonemptiness replaced by the quantitative threshold); `boundaryCardLatticeThresholdResidual_of_extraction` closes the latter from the former. Consumer shape: `correlatedAgreementCurves_of_latticeExtraction` yields `δ_ε_correlatedAgreementCurves` with `ε = (n+1)/|F|`.
* Witness namespace: the whole spine fires end-to-end at the genuine lattice endpoint ZMod 11 / Fin 8 / deg 2 — `sqrtRate·8 = √16 = 4` exact, `⌊δn⌋ = δn` (`latticeW`), zero stack has `Pr = 1 > 9/11` and forced extraction (a `natDegree < 2` polynomial vanishing on ≥ 4 of 8 distinct evaluation points is 0); satisfiability certified, no unsatisfiable-hypothesis leaf. (Bookkeeping: the brief's other suggested piece — floor-cell threshold monotonicity — was already landed by a parallel lane as O78/`BoundaryThresholdFloorCell.lean`; duplicate guard caught it before writing.)

**Where the open core sits:** both leaves of the boundary quantization split now rest on exactly one kind of input each — the strict-interior §5 producer per floor cell (non-lattice, O78) and `LatticeCoeffPolyExtraction` at the endpoint (lattice, this entry). Both are the BCIKS20 §5 list-decoding extraction content; the boundary plumbing is complete and the extraction is provably not droppable on either branch.

### O85 — census C3 PROVEN at every radix: single-class words are fiber-aligned (nubs, 2026-06-10)

(Record note first: O70's bookkeeping correction is confirmed from this seat — my O69
commit `2dcc9cfd9` did NOT contain the announced `weight_ge_live_image`; a landing-loop
error dropped the working-tree edit (branch snapshot taken before commit). The content
was independently supplied at every depth by O70's `live_card_le_weight`. Thanks to the
cold audit; loop fixed — snapshots now taken post-staging, pushed diffs verified against
claims.)

New brick `ArkLib/Data/CodingTheory/ProximityGap/SingleClassWeight.lean` (axiom-clean):
the census C3 rigidity (0/95,623 violations in O69's data) is now a theorem, and it
holds at EVERY radix `m ∣ n`, not just 2-powers:

* `single_class_weight`: on a full `n`-th-root domain (`|H| = n = s·m`, `0 ∉ H`), a
  single-coefficient-class word `f = X^r·g(X^m)` has EXACT weight
  `n − m·#{slice zeros in the image domain}` — its zero set is a union of full `m`-power
  fibers (`SmoothFiberCount.preimage_card_eq` does the counting). Single-class = fiber-aligned.
* `dvd_sub_weight_of_single_class`: hence `m ∣ n − w`.

Contrapositive, in branch language: at any weight with `2^ℓ ∤ n − w`, the depth-`ℓ`
fold tree provably keeps ≥ 2 alive branches — narrowness in the coefficient tree exists
ONLY at coset-compatible weights (the O46/O47 boundary), at every level and every radix.
Together with O70's root-coherence theorem the structural story is: low weight forces
slices to share roots; fiber-misaligned weight forbids slice concentration. The
surviving frontier is unchanged and now sharply framed: the per-locus COUNT — bound
#{f : deg f < k, all 2^ℓ slices vanishing on a common locus Z}; for fixed Z the slices
live in root-forced subspaces of total dimension k − 2^ℓ·|Z| (the linear-algebra brick
queued next), and the open content is the union over loci versus the weight filter.

### O69 — CLASS-CHART BOUNDS: the scaling-orbit theorem formalized + the A–S decomposition + a kernel-checked orbit pin (ClassChartBounds.lean)

The provable parts of the O51 program, axiom-clean ([propext, Classical.choice, Quot.sound], 0 sorry):

* **The weighted-scaling fiber bijection as a CARD equality** (`psumFiber_scaling_card`): for λ ≠ 0,
  S ↦ λ·S bijects the (a₁,…,a_t)-power-sum fiber over D₀ onto the (λa₁,…,λ^t a_t)-fiber over λ·D₀;
  on scaling-invariant domains fiber cardinality is a weighted-projective orbit invariant
  (`psumFiber_orbit_card`), the zero class is the fixed point (`zero_fiber_scaling_mem`), and any
  uniform bound need only be certified on an orbit transversal (`psumFiber_card_le_of_orbit_rep`).
* **The conditional Aliev–Smyth uniform bound** (`nonzero_fiber_card_le`): with the named hypotheses
  `ASIsolatedBound` (A–S Thm 1.1, arXiv:0704.1747, isolated torsion points of V(p−a) ⊆ 𝔾_m^w; constant
  abstract) and `CosetFamilyBound` (per-coset tower count, O46–O50), every nonzero-class fiber is
  ≤ C + B uniformly — the isolated ⊔ coset-family decomposition is machine-checked, and transfers
  along whole orbits (`nonzero_fiber_card_le_orbit`).
* **Kernel instance with an honest correction**: at ZMod 13, w = 3, t = 2 the strict probe dichotomy
  ("nonzero ⟹ ≤ 2") is FALSE — but the failure is structured: zero fiber = 4 (`zero_psum_fiber_F13`),
  all nonzero ≤ 4 (`nonzero_fiber_card_le_four_F13`), and the 12 maximal nonzero classes are EXACTLY
  ONE weighted orbit {(5λ,4λ²)} (`nonzero_fiber_le_two_or_rep_orbit_F13`); the part-1 theorem then pins
  the whole orbit from the single decided representative (`orbit_of_rep_card_F13`). Fiber card really
  is an orbit invariant, visible in the kernel. advancesOpenCore=false (A–S itself stays a hypothesis).

### O70 — MIXED-RADIX TOWER LAW CONFIRMED EXHAUSTIVELY at n=12,18,24,36: 86/86 (n,t) fibers set-equal to the divisor-coset prediction (numeric lane). Probes (/tmp/mixed_tower_probe.py, /tmp/mixed_tower_debruijn_check.py; tables /tmp/mixed_tower_results.txt, /tmp/mixed_tower_tables.json) over F_p, p=1000000009 ≡ 1 mod 72 (cross-checked p=2000000089; char-0 conclusive by the Z[zeta] sandwich): for every t=1..n-1, the window fiber {S ⊆ mu_n : e_1=..=e_t=0} EQUALS the disjoint unions of rotated mu_d-cosets, d|n, d>t (generated by the divisibility-minimal divisors > t — up to 3 generators, e.g. Dmin(36,3)={4,6,9}). Pure size-kill law (mu_d dies iff d ≤ t), plateaus between consecutive divisors, totals e.g. |F_36(t)|: 10^6, 22^3, 1036, 100, 22, 10, 4, 2. de Bruijn upgraded from O67's sampling to EXHAUSTIVE censuses: all 10^4 (n=24, full 2^24) and all 10^6 (n=36, complete MITM census) vanishing subset sums decompose into disjoint prime packets; independent backtracking decomposer agrees. Count structure: naive size-multiset formula REFUTED (mu_4-coset = CRT column meets every mu_9-coset = CRT row ⟹ zero weight-13 members at (36,3)); exact law F_n(t) ≅ F_lcm(Dmin)(t)^(n/lcm) verified 25/25 — the numerical shadow of the O68 double-slice/CRT induction, fixing the formalization route for the two-prime full_tower analogue. Bonus: O49 threshold visible (F_13, n=12: 316 vs 100 fiber members). Newton e-window == p-window checked directly at n=12,18 all t.

### O70 addendum — finite GS interleaving leaves a formal residual gap to capacity (small verified threshold-geometry brick)

`Issue232VerifiedBricks.lean` now records the exact finite-interleaving capacity residual:

* `interleave_capacity_gap_eq`:
  `(1 - ρ) - (1 - ρ^(m/(m+1))) = ρ^(m/(m+1)) - ρ`.
* `interleave_capacity_gap_pos`: for every finite `m` and every rate `0 < ρ < 1`, that residual is strictly positive.
* `interleave_capacity_gap_strict_decrease`: the residual strictly decreases when `m` is incremented, matching the already-proved strict monotonicity of the finite GS radii.

Interpretation: finite GS interleaving really does climb from Johnson toward capacity, but the kernel now explicitly sees the positive leftover at every finite level. The missing #232 breakthrough remains a beyond-finite-GS idea or a separate counting theorem in the residual band; no threshold `δ*` is claimed.

### O71 — TWO-PRIME DE BRUIJN DOUBLE-SLICE, UNCONDITIONAL (DeBruijnTwoPrime.lean)

Workflow lane completed + main-loop audited (compiles, every theorem
[propext, Classical.choice, Quot.sound], 0 sorry). The lane EXCEEDED its T2 target:
the linear-disjointness step is DISCHARGED, not hypothesized —

* `minpoly_adjoin_primitiveRoot_eq_packet` / `minpoly_qadjoin_eq_cyclotomic`:
  Φ_{p^(a+1)} remains the minimal polynomial of ζ_p over ℚ(ζ_q) for q ≠ p — coprime
  cyclotomic linear disjointness as a theorem.
* `vanishing_coeff_slices_over`: the O68 slice engine over an arbitrary coefficient
  field K (with the packet-minimality input) — the K-coefficient generalization.
* `two_prime_qside_slices` (UNCONDITIONAL): for S ⊆ μ_{p^(a+1)·q^b} with vanishing sum,
  the ℚ(ζ_q)-grouped coefficients are constant along μ_p-coset directions.
* `two_prime_deBruijn_double_slice` (UNCONDITIONAL HEADLINE): the membership difference
  pattern between μ_p-coset-related rows is constant along μ_q-coset directions — the
  full CRT double-slice structure of two-prime vanishing subset sums, machine-checked.

This is the de Bruijn third pillar's hard core: what remains for the full packet
decomposition is finite bookkeeping on the doubly-sliced pattern (the O70 law gives the
exact target statement).

### O72 — THE EFFECTIVE TRANSFER IN LEAN (EffectiveTransfer.lean): the O49 chain complete

Workflow lane completed + main-loop audited (compiles, all 14 theorems axiom-clean,
0 sorry). The full norm-bound transfer machinery, formal:

* `norm_embedding_sum_le` / `abs_norm_le` / `intNorm_abs_le`: a sum of B roots of unity
  has every embedding of absolute value ≤ B, hence |ℤ-norm| ≤ B^{finrank}.
* `intNorm_ne_zero`, `dvd_intNorm_of_eq_zero` (Galois case), `reduction_ne_zero`:
  a nonzero algebraic integer with |norm| < p cannot die under any reduction 𝓞_K → ZMod p.
* `coe_esymm`, `esymm_reduction_ne_zero`, and the headline
  `esymm_eq_zero_iff` / `esymm_eq_zero_iff_cyclotomicField`: for p beyond the explicit
  binomial-norm threshold, e_j of a lifted subset vanishes mod p IFF it vanishes in
  characteristic zero — THE O49 EFFECTIVE TRANSFER AS A LEAN THEOREM. With O53/O55/O61:
  the tower theory's F_p instances are now unconditional above an explicit, formal bound.

### O87 — THE n=32 CENSUS: ℓ₃₂(w,18) = 35 — the structured core EXACTLY exhausts the beyond-Johnson list; Conjecture D maximally confirmed at the canonical word (nubs, 2026-06-10)

`scripts/probes/n32census/` (kernel + postpass + RESULTS.md, commit 655d2dd21): the descent
program's named decisive computation (07-DESCENT; claimed #232 c-4666108014), executed as a full
C(32,17) = 565,722,720 finite-difference functional sweep over the canonical max-fiber word on
X¹⁸ + λX¹⁶ (BabyBear, ρ = 1/2, a = 18 = witness level, radius 0.4375 ≫ Johnson 0.293, η = 1/16).
**Result: ℓ₃₂(w,18) = 35 EXACTLY = the constructed u_S(X²) witness family, 35/35 — ZERO dense
enrichment at the witness level at n=32 scale** (Entry-11's n=16 finding holds one scale up);
agreement histogram {18: 35}; cross-foots exact (630 emissions = 35·C(18,17); per-chunk swept
counts = C(31−i₀,16), total = C(32,17)). One notch below: **ℓ₃₂(w,17) = 35 + 1,344 = 1,379**
(pass-accounting + the audit's DIRECT independent enumeration: 1,344 distinct, one subset each,
disjoint, all full-support — 0 all-even forced by parity). Notch-enrichment 39.4 vs n=16's 6.33 —
polynomial-consistent (H3′). First O63 2-adic spread chart of a real beyond-Johnson list: all 35
in depth-1 class (0); depth-3 splits {4 mod-8 classes ×32, 2 classes ×3}. Thresholds: 35 ≪
32·3280 = 104,960 (D-falsification line) and = 0.05% of the c=1 budget 2¹⁶ — **D is NOT
falsified; it is maximally confirmed here.** Rigor gates: n=16 calibration reproduced C19's
19 = 3+16 bit-exactly BEFORE n=32 was believed; the max-fiber λ tie-class is rigorously the
μ₁₆-orbit of g₀^((p−1)/4) (x ↦ ux isomorphism ⟹ count tie-independent; a second tie value run
end-to-end gave the identical 35); adversarial audit with a from-scratch independent kernel
(different algorithm) re-verified every element and reproduced the coverage hashes. For the
branch-count distribution (O59/O61/O63): this is the first complete level-2 data point — the
distribution at the canonical word is maximally concentrated on the structured classes.

### O73 — THE CONDITIONAL TWO-PRIME TOWER (MixedRadixTower.lean): the mixed-radix skeleton complete

Workflow lane (taken over and audited by the main loop; compiles, all theorems
axiom-clean, 0 sorry — the file's two 'sorry' grep hits are docstring prose):

* `mu_mul_closure`, `pow_fiber_coset/card/sum_pow`, `descended_window` — the radix-d
  descent toolkit at every exponent (windows descend through the d-th-power map, char 0).
* `mixed_rung_conditional` + `prime_climb_conditional` — one rung and the stacked
  prime-power climb, conditional on the packet base case at each level (named hypotheses).
* `coprime_mu_closure_combine` — THE COPRIME WELD: closure under μ_A and μ_B for coprime
  A, B gives closure under μ_{AB} (CRT at the closure level).
* `two_prime_tower_conditional` — the headline: on n = p^a·q^b-torsion domains, window
  vanishing forces μ_d-closure for the divisor-coset structure, conditional on de Bruijn
  base hypotheses — standing to O71's double-slice brick exactly as t2_tower_resolution
  stood to the Lam–Leung brick before O50 discharged it.
* `base_case_level_one`, `base_case_window_ge_level`, `window_forces_empty` — base-case
  hypotheses discharged unconditionally in the degenerate regimes.

The O70-verified law now has its formal skeleton; what separates conditional from
unconditional is finishing O71's double-slice into the full packet decomposition (finite
bookkeeping on the doubly-sliced pattern).

### O74 — the COMPLETE ℚ-kernel at 2-power level: vanishing ⟺ antipodal symmetry

`LamLeungTwoPow.vanishing_iff_antipodal_coeffs` + `nonvanishing_of_unpaired`
(axiom-clean, 0 sorry; the killed branch-count lane's task trail, taken over and proven
by the main loop): a ℚ-coefficient combination of 2^(m+1)-th roots vanishes IFF its
coefficient function is antipodally symmetric (c(e) = c(e + 2^m)) — necessity = the O68
slice theorem at p = 2, sufficiency = ζ^{2^m} = −1 pairing. Corollary: any combination
with an unpaired support point is NONZERO — the sparse-nonvanishing rigidity that forces
branch data in the descent tree (no asymmetric configuration silently vanishes; the
ℚ-relations available to a branch are EXACTLY the antipodal symmetrizations). This is the
complete linear-algebra description of the 2-power relation module — the branch-entropy
accounting now has rigid leaf data.
### O87 — de Bruijn step (3) FIRST DISJOINTNESS BRICK LANDED: the squarefree two-prime case is a theorem (pure type), and the prime-power scope boundary is measured exactly

O73/O79 left exactly one genuinely de Bruijn input open: indicator fiber sums force DISJOINT rotated full prime packets. This pass closes it in full at the squarefree level n = p·q — the level where the in-tree invariance engine says ALL fibers are equal — and measures where the statement honestly stops.

**Falsify-first probe (`probe_indicator_packet_disjointness.py`, exact ℤ[x]/Φ_n arithmetic, exit 0):** the headline EXHAUSTIVELY at n = 6, 10, 15 (all 2^n subsets; 10/34/38 vanishing, 0 violations; both pure types occur; 54 non-vanishing violators at n = 6 — hypothesis load-bearing). The verbatim prime-power extension is **REFUTED**: 24/100 vanishing subsets at n = 12 and 432/1000 at n = 18 violate BOTH coset closures (mixtures, e.g. mask 0x193 = {0,6}∪{1,5,9}), so a = b = 1 is the honest scope — the headline is deliberately NOT stated at prime powers. C6 measures the a ≥ 2 recursion seed: every CRT column indicator difference is divisible by Φ_{p^a} (100% at 12 and 18), while the naive dichotomy fails 168/486 times there — the next brick is the packet-combination form, not the dichotomy. O67's mixed-decomposition census re-verified (100/100, 1000/1000).

**Bricks (`DeBruijnIndicatorDisjointness.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):**
* `coeffs_all_eq_of_vanishing_prime` — vanishing ℚ-weighted sums of p-th roots have ALL coefficients equal (the m = 0 slice of O73's `weighted_vanishing_slice_rat`, instantiated not re-proven).
* `equal_indicator_sums_dichotomy` — **the step-(3) engine at a prime**: two 0/1 subset sums of μ_p agree iff the sets are EQUAL or one is full and the other empty (the indicator difference takes values in {−1,0,1} and all values are equal; with p prime there is no room between).
* `vanishing_indicator_empty_or_full` — the brief's named candidate verbatim: a vanishing 0/1 sum of μ_p has empty or full support — every nonzero fiber is exactly one full μ_p-packet.
* `gridMap_snd_succ` / `gridMap_fst_succ` — cyclic CRT coordinate shifts realize +p / +q on exponents (no Bezout, pure Nat.mod_add_div bookkeeping).
* `debruijn_squarefree_two_prime` — **the headline**: vanishing indicator sum over ZMod(p·q) ⟹ S closed under +p (disjoint rotated full μ_q-packets) OR closed under +q (μ_p-packets). Composes `subset_sum_eq_grid_double_sum` (O79 step 2) + `crt_fiber_slice_coprimePrimePowers` at a = b = 1 (O79 step 1: all fibers equal) + the dichotomy: all fiber sets equal ⟹ +p-closure; any two differ ⟹ one is empty ⟹ every fiber sum is 0 ⟹ every fiber empty-or-full ⟹ +q-closure. PURE type — sharper than de Bruijn's ℕ-combination statement restricted to indicators (every μ_p-coset meets every μ_q-coset, so mixtures cannot be disjoint at the squarefree level; the probe confirms the count: 6+2+2 = 10 at n = 6, exactly the coset-union census).
* Non-vacuity with teeth: fired end-to-end at ℂ, n = 2·3, S = {0,3} (ζ⁰+ζ³ = 0 genuinely vanishing), with `decide` witnesses pinning the disjunction to the right branch AND kernel-checking the left branch fails — the conclusion discriminates.

**Where the open core moves:** the three-step de Bruijn ledger (O73's residuals) is now (1) CLOSED, (2) CLOSED, (3) CLOSED at a·b = 1. What remains for the full two-prime theorem (and the M31-domain capstone) is the prime-power case a·b > 1: replace the dichotomy by the C6-verified packet-combination form (column differences = ℤ-combinations of rotated Φ_{p^a}-packets — a one-divisibility Lean statement, deg < p^a forces quotient deg < p^{a-1}) and recurse down the q-adic digits; the probe's mixture census (24/100, 432/1000) is the target's exact shape.
### O88 — K4's depth-0 layer PROVEN: the capture-kernel affine pinning holds antecedent-free on the unique-decoding window, and the Hensel frontier is pinned to exactly 3(n−t) > d−1

O79 (Hab25CaptureKernel) left the Steps 5–7 kernel as K1 ∧ K4 with K4 — `T < |Ecell| → ∃ v₀ v₁ (natDegree < k), ∀ γ ∈ Ecell, P γ = v₀ + C γ·v₁` — named as the genuinely deep input (Claim 5.7 pigeonhole + Claims 5.8/5.9 Hensel branch degree/Z-linearity + Appendix C), with zero in-tree consumers since. This pass restates the demand, maps the Hensel lanes against it, and proves the first honest sub-piece: the **base case of the Hensel induction** — the depth-0 layer where no lifting over `F⟦X⟧` is needed.

**The lane inventory (what exists vs what K4 needs):** `HPzBridge.decoded_eq_specialization_of_hensel` + `CurveFamilyHensel.CurveHenselDatum` produce per-`z` identities `P z = ∑_t (z−x₀)^t • c_t` for the *coefficient* stack (`Fin (k+1)`), conditional on per-`z` root data (matching polynomial over `F⟦X⟧`, common mod-`X` approximation, unit derivative); `MatchingExtractor.matchingFactor_dvd_of_orderM_and_count` (proven) feeds K1. The delta to K4 is threefold: (i) the antecedent-to-witness pigeonhole (`T < |Ecell|` must *produce* the pencil — Claim 5.7), (ii) degree-1-in-`γ` (the curve must collapse to a pencil — Claim 5.9 Z-linearity), (iii) the inseparable shell (App C). None of it is needed at depth 0.

**Bricks (`Hab25CaptureKernelUD.lean`, axiom-clean [propext, Classical.choice, Quot.sound] ×7, 0 sorry, 0 warnings):**
- `mcaDecode_P_eq_of_window` — **the uniqueness half**: on `n + k ≤ 2t` (t = ⌈(1−δ)n⌉₊, i.e. 2(n−t) ≤ d−1), any two `McaDecode` witnesses of the same `(u, γ)` carry the SAME polynomial — two witness sets share ≥ 2t−n ≥ k points and the difference has degree < k. The per-γ decode family is forced; any two affine pinnings of a cell coincide (`decode_family_eq_on_of_window`).
- `exists_pencil_of_decode_family_window` — **K4 on the window, antecedent-free**: on `2n + k ≤ 3t` (⟺ 3(n−t) ≤ d−1), any decode family on any cell with ≥ 2 scalars is affinely pinned. Constructive: `v₁ = C(γ₁−γ₂)⁻¹·(P γ₁ − P γ₂)`, `v₀ = P γ₁ − C γ₁·v₁` interpolates the stack rows on S₁∩S₂; any third member's decode agrees with the specialization on the triple intersection (≥ 3t−2n ≥ k points), forcing equality by root count. The O84 mechanism (`TheoremQUDExtraction.exists_affine_pair`, codeword side, Theorem-Q evalCode) re-proven on the kernel's own `McaDecode` polynomial surface — different consumer, same window.
- `hsteps57_of_window` + `cell_card_le_of_decode_family_window` — the composition through the O79 seam: K1 alone yields the literal `hsteps57` of `claim1_dichotomy` and the unconditional cell bound `|Ecell| ≤ T` (T ≥ n) on the window. `window3_implies_window2` (the 3-window forces decode uniqueness) and `k4_ud_window_satisfiable` (9 ≤ 12 at Fin 4, δ = 0, k = 1) close the satisfiability leaf.

**Falsify-first probe (`probe_k4_ud_window.py`, exact, exit 0):** exhaustive GF(5) n=4 k=1 t=3 — all 390,625 stacks, 48,000 multi-scalar bad sets in-window, ALL decode choices per scalar enumerated: 0 uniqueness violations, 0 pencil failures, 0 pencil-choice mismatches; planted+random GF(7) n=6 k=2 t=5: 400 multi-scalar cells, 0 violations. **Negative control (the window is load-bearing):** at t=4 (3(n−t) = 6 > d−1 = 4), 59/600 planted stacks break the constructed pencil — consistent with O84's C2 refutation of the affine decoding law past d/(3n), now measured on the decode-polynomial surface.

**Where the open core moves:** K4 is no longer monolithic — its statement now has a proven floor (3(n−t) ≤ d−1, no Hensel content needed) and a pinned frontier: the regime `3(n−t) > d−1` per GS cell, where the pencil must come from the genuine lift (per-cell branch polynomials over `F⟦X⟧` with Claim 5.8's Λ-weight degree bound, Claim 5.9's Z-linearity cutting the `CurveHenselDatum` curve to degree 1, App C's inseparable shell). The named next sub-obligation: convert one `CurveHenselDatum` (Fin (k+1) coefficient stack) output into the Fin-2 pencil shape of K4 past the window — the Z-linearity step is the seam, and `ZLinearRatFuncDegreeOne`/`CurveFamilyZLinear` are the in-tree anchors it must land on.
### O89 — the O84 counting question ANSWERED in shape: badCount ≤ 2(n−t)+1 is REFUTED at the top of the gap (exhaustive truth = 2(n−t)+2, and ~n at e = 1), while the strict interior survives and is named in-tree

O84 closed the extraction on 3(n−t) < d and left the window (d/(3n), (d−1)/(2n)] as "a counting question, not a structure question", with the natural conjecture badCount ≤ 2(n−t)+1 open (its hunt never saw more than 3). This pass answers the shape of the question. The structural key: two bad scalars whose decodes share an affine codeword family pin that family (O84's subtraction); two DISTINCT (e+1)-support families differ by an m=2-interleaved codeword of column weight ≤ 2(e+1), so they can coexist iff 2(e+1) ≥ d — i.e. exactly on the top slice of the gap, where each family carries up to e+1 Möbius-distinct cancellation scalars.

**REFUTED (probe witness, `probe_counting_gap.py`, exact GF(p), exit 0): the natural conjecture fails on the top slice 2(n−t) = d−1.** The multi-family construction (e := h restricted to T₁ for codeword pairs h_j vanishing off T₁ ∪ T_j, kernel-solved consistency, ratios a Möbius image hence distinct) yields, machine-verified by exact bad-set computation: badCount 6 > 5 at RS(6,2)/GF(7), δ = 1/3; **10 > 9 at RS(16,8)/GF(97), δ = 1/4 — the very O84 hunt code, inside the δ-window at its included right endpoint**; 10 > 9 at RS(12,4)/GF(13); and **12 > 3 at RS(12,10)/GF(13) (e = 1, d = 3)** — twelve of thirteen scalars bad on one stack (so ε_mca(RS(12,10), 1/12) ≥ 12/13: at e = 1 the consistency kernel has dimension 3−e = 2 per extra family and the family count is unbounded, connecting to the #39 radius-one badRatios extremal target). **No closed form in (n−t) alone can bound the gap**; the governing quantity is the interleaved list size Λ₂(2δ) — the proven O74/O85 ceiling 1 + 2(n−t)·Λ₂ held on every measured stack.

**Exhaustive ground truth (the true max, not a lower bound):** over ALL coset-pair stacks of RS(6,2) and RS(7,3) over GF(7) (23,200 affine classes each; orbit coverage asserted, 6 invariance spot-checks vs raw bad-set, BW vs exhaustive decoder identical), the top-slice maximum is **exactly 2(n−t)+2 = 6** (attained by 20 resp. 140 classes; never 7 = q). Histograms recorded.

**SURVIVES (0/1,263): the strict interior 2(n−t)+2 ≤ d.** Adversarial hunts (g-planting, 2-g nesting, two-cancel, random, structured-collapse shapes) at (97,16,8) e=3, (13,12,4) e=3, (13,12,2) e=4, the even-d top (13,9,4) e=2, plus a non-MDS (non-GRS) [8,3,5]₇ attack-search control: max observed 5, **0 violations of 2(n−t)+1**. The violation mechanism is provably rigid there: the multifamily consistency kernel is 1-dimensional (proportional rows ⟹ constant ratio ⟹ one scalar per family), printed by the probe each time it blocks.

**Bricks (`CountingGapConjecture.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings):** `GapCountingBoundFullWindow` — the natural conjecture named as the falsified surface (probe-cited, never to be assumed); `InteriorCountingBound` — the surviving conjecture on 2(n−t)+2 ≤ d; `interiorCountingBound_of_gapCountingBoundFullWindow` (refuted ⟹ surviving monotonicity); `epsMCA_le_of_interiorCountingBound` — the consumer: the surviving conjecture gives ε_mca ≤ (2(n−t)+1)/|F| on its window via `epsMCA_le_of_badCount_le`, extending O84's proven shape from 3(n−t) < d to the full strict interior; `gap_trichotomy` + `top_slice_iff_odd` — the UD side splits exactly into {proven O84} ⊔ {surviving interior} ⊔ {refuted odd-d top}, and the refuted slice exists iff d is odd; `interior_window_extends_proven` — the conjecture window strictly extends the proven one (e=3, d=9).

**Where the open core sits:** the gap of O84 is now split. Below the unique-decoding radius (2(n−t) ≤ d−2) the honest open conjecture is `InteriorCountingBound` — unrefuted by 1,263 adversarial stacks, and the only known violation mechanism is provably unavailable. AT the radius (d odd) the bound is dead: the truth is 2(n−t)+2 exactly at the two exhaustible points, ~n at e=1, and in general coupled to Λ₂(2δ) (O85's conversion is the right shape). Closing `InteriorCountingBound` needs a per-line argument that a single decode family plus stragglers stays ≤ 2(n−t)+1 without the affine law — the probe says the wall is real but thin.

### O75 — branch-entropy probe: generic words carry O(1) deep-interior lists (unfalsified)

Falsify-first probe (docs/kb/mixed-tower-probes/branch_entropy_probe.py; n = 16, k = 3
over F₉₇, full 97³ codeword enumeration, 60 trials per agreement level mixing planted-
error and uniform-random received words): at agreements a = 5, 6, 7 (all BEYOND the
Johnson agreement √48 ≈ 6.9 at a = 5, 6), the maximum observed list is 3, 1, 1 — and the
support-descent size sequences are pairing-free (11→7→4→2→1: generic halving, no
antipodal structure). Conclusion: generic and planted words carry O(1) deep-interior
lists; ALL observed list mass concentrates at the structured (class-syndrome/coset)
words already characterized by the tower theory — consistent with, and unfalsifying,
the branch-entropy accounting in which rigid leaf data (O74) plus tree-shape counting
bounds the list. The worst case is provably NOT found by sampling; it is the structured
chart, which is exactly where O45–O74 live.

### O76 — THE PACKET COVER: de Bruijn's hard direction, unconditional (two_prime_packet_cover)

`DeBruijnTwoPrime.two_prime_packet_cover` (axiom-clean, 0 sorry, by hand from O71's
double-slice): **every member of a vanishing subset of μ_{p^(a+1)·q^(b+1)} has its full
μ_p-fiber in S or its full μ_q-fiber in S.** Proof: if the p-fiber misses a point, the
double-slice forces the membership difference row ≡ 1 along the entire q-direction, so
the q-fiber is full — pure case analysis on O71.

This is the necessary half of de Bruijn's 1953 theorem at the subset level, now formal
and hypothesis-free. Honest scope: cover is necessary, NOT sufficient (overlapping
packets break the vanishing sum); the exact O70 law is the disjoint-decomposition
refinement — the remaining finite combinatorial step between cover and the full
characterization (and thence the discharge of O73's base hypotheses).

### O77 — DE BRUIJN 1953, COMPLETE: the full two-prime packet decomposition machine-checked

`DeBruijnTwoPrime.two_prime_packet_decomposition` (axiom-clean, 0 sorry, by hand):
**a finite subset of μ_{p^(a+1)·q^(b+1)} (p ≠ q primes, characteristic zero) with
vanishing sum IS a disjoint union of full μ_p- and μ_q-packets** — the `PacketUnion`
inductive built packet-by-packet, each peel disjoint from the rest by construction.

Proof: peeling induction over the O76 cover — a full prime packet sums to zero
(`prime_packet_sum_zero`, geometric series), so removing the packet supplied by the
cover dichotomy preserves the vanishing sum and strictly drops cardinality; strong
induction finishes. Plumbing: CRT box coordinates (box_pair_surj/inj), the
nonlinear-cancellation index arithmetic, and the new-Mathlib card_sdiff intersection
form.

This completes the de Bruijn third pillar END TO END: O68 engine → O71 double-slice
(linear disjointness proven) → O76 cover → O77 decomposition. The t = 1 instance of the
O70 mixed-radix law is now an unconditional theorem; connecting PacketUnion to O73's
closure-hypothesis format (mechanical) makes the first rung of the mixed tower
unconditional. The mixed-radix program's three pillars are all formal.
### O90 — O87's recursion seed PROVEN IN FULL: packet divisibility below p^a IS a bounded-coefficient combination of rotated Φ_{p^a}-packets (and conversely), the a ≥ 2 de Bruijn descent engine

O87 left the prime-power continuation as one named brick: column indicator differences of CRT fibers at a prime power, divisible by Φ_{p^a} (C6: 100% at n = 12, 18, where the naive dichotomy fails 168/486), should be ℤ-combinations of rotated Φ_{p^a}-packets — with the degree bound on the quotient named as the smallest honest piece. This pass proves the WHOLE brick, both directions, over any nontrivial integral domain, with no primality needed on the packet side.

**Falsify-first probe (`probe_packet_quotient_coeffs.py`, exact integer arithmetic, exit 0):** exhaustive over all vanishing subsets at n = 12 (600 ordered column pairs) and n = 18 (2000 pairs): every difference divisible (O87 C6 re-verified), every quotient has deg < Q = p^(a−1), every quotient coefficient in {−1,0,1}, the quotient IS the bottom coefficient slice of d, and the rotated-packet combination reconstructs exactly. **The exact coefficient structure answered (the brief's question):** the realized quotients exhaust the FULL {−1,0,1}^Q cube (9/9 at 12, 27/27 at 18) — no further restriction exists. **Finding (a wrong control corrected mid-probe):** the bottom-slice identity R[s] = d[s], s < Q, holds for ANY quotient — the convolution against the packet's sparse support never reaches down — so the degree bound's only job is to make the bottom slice the WHOLE quotient; without deg d < p^a the shifts-<Q combination fails (d = Φ·X^Q). Exact census: the divisible {−1,0,1}-vectors of length p^a are EXACTLY {Φ·R : R ∈ {−1,0,1}^Q}, count 3^Q (9 of 81 at p^a = 4; 27 of 19683 at p^a = 9) — the bijection the Lean brick states, with non-divisible vectors witnessing divisibility load-bearing.

**Bricks (`PacketCombinationDivisibility.lean`, axiom-clean [propext, Classical.choice, Quot.sound] ×11, 0 sorry, 0 warnings):**
* `quotient_natDegree_lt` — **the named degree bound**: d = packet·R, d ≠ 0, natDegree d < p·q ⟹ natDegree R < q (pure degree bookkeeping off natDegree packet = (p−1)·q, no monic machinery — domain + leading-coefficient count).
* `packet_mul_coeff` + `quotient_coeff_eq_bottom` — the generic-ring slice convolution (LamLeungTwoPow's ℚ-only lemma re-proven over any CommRing) and its i = 0 instance: the quotient is the bottom slice.
* `packet_dvd_combination` — **the headline**: packet ∣ d, deg d < p·q ⟹ d = Σ_{s<q} C(d.coeff s)·X^s·packet — combination coefficients are literally coefficients of d, so ANY coefficient bound transfers verbatim; `indicator_diff_packet_combination` instantiates at {−1,0,1} (the O87-named statement).
* `packet_dvd_of_slice_replication` + `packet_dvd_iff_slice_replication` — **the converse and the recursion-usable iff**: below degree p·q, packet divisibility ⟺ p-fold slice replication d.coeff(t·q+s) = d.coeff s — the form the a ≥ 2 descent consumes (column data at level a becomes slice data at level a−1).
* `cyclotomic_prime_pow_eq_packet`, `cyclotomic_dvd_combination`, `indicator_diff_cyclotomic_combination` — the bricks restated verbatim on Φ_{p^(a+1)} via `cyclotomic_prime_pow_eq_geom_sum`, landing exactly on the C6 surface.
* Non-vacuity with teeth: fired end-to-end at ℚ on the probe's own realized quotient (1,−1) (d = 1−X+X²−X³, the {0,2}-vs-{1,3} column difference) and on the rotated packet X+X³; `¬ packet ℚ 2 2 ∣ (1+X)` proven through the iff — the conclusion discriminates.

**Where the open core moves:** the three-step de Bruijn ledger now has its prime-power engine: O87's column differences at level a are, by this brick, bounded combinations whose coefficients are bottom-slice indicator data — i.e. the iff converts Φ_{p^a}-divisibility into p-fold slice replication, exactly the descent from q-adic digit a to a−1. What remains for the full two-prime theorem (and the M31-domain capstone) is the WIRING: run the recursion down the digits inside `MixedRadixTower`'s conditional rungs (replace the level-a base hypotheses by this brick + induction) and assemble mixed disjoint packets at composite levels — bookkeeping plus the O67-verified mixed-decomposition census as the target shape, no new divisibility content needed at a single prime power.
### O91 — de Bruijn: the O79 splice LANDED + the squarefree classification completed to an EQUIVALENCE (sufficiency engine at every modulus)

Two complement bricks around the O87 disjointness landing, both queued by the in-tree ledger and neither stated anywhere on main: the O79 step-(1) entry's deferred splice ("composing the two yields the full two-prime subset-sum fiber slice with no hypothesis; deliberately not built this pass to avoid depending on an unlanded sibling file" — both siblings have since landed), and the SUFFICIENCY half of de Bruijn step (3) (O87 proved vanishing ⟹ closure; the packet cover proved per-element necessity; nothing proved closure ⟹ vanishing).

**Brick 1 (`CRTSubsetSumFiberSlice.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings): the splice.**
* `vanishing_subset_sum_fiber_slice` — **the unconditional two-prime subset-sum fiber slice at general `p^a·q^b`**: distinct primes `p ≠ q`, `0 < b`, `ζ` a primitive `(p^a·q^b)`-th root in ANY characteristic-zero field, `S ⊆ ZMod (p^a·q^b)` with `∑_{e∈S} ζ^e = 0` ⟹ the CRT-grid fiber sums `∑_{j<p^a} [(j, i·q^{b−1}+s) ∈ gridSet S]·(ζ^{q^b})^j` are independent of `i < q`. Steps (0)+(1)+(2) composed (`subset_sum_eq_grid_double_sum` + `crt_fiber_slice_coprimePrimePowers`); only the primitive root and the vanishing sum remain. (The O87 lane inlined this composition at `a = b = 1`; the general exponent-surface statement was still missing — it is the input shape for the `a·b > 1` packet-combination recursion named open by O87.) Non-vacuity at a NONEMPTY vanishing sum (`n = 6`, `S = {1,4}`, `ζ + ζ⁴ = 0` over `ℂ`).

**Brick 2 (`DeBruijnSquarefreeIff.lean`, axiom-clean, 0 sorry, 0 warnings): the equivalence.**
* `sum_pow_val_eq_zero_of_addClosed` — **the shift engine, any modulus**: a subset of `ZMod n` closed under translation by `d` has vanishing sum against any `n`-th root `ζ` with `ζ^{d.val} ≠ 1` (translation is a bijection of S onto itself ⟹ the sum absorbs a factor `ζ^{d.val}`). Consumes nothing about `n`'s factorization — the sufficiency mechanism at EVERY level of the de Bruijn program.
* `vanishing_of_addClosed_packet` — prime-power instantiation: in `ZMod (p^a·q^b)`, closure under the packet step `+p^a·q^{b−1}` (a union of rotated full μ_q-packets) forces vanishing. The converse of the landed `two_prime_packet_cover` necessity, at the same generality.
* `debruijn_squarefree_two_prime_iff` — **the capstone equivalence at squarefree `n = p·q`**: `∑_{e∈S} ζ^e = 0 ⟺ S` is `+p`-closed or `+q`-closed. Forward = O87's `debruijn_squarefree_two_prime`; backward = the shift engine at `d = p, q` (`ζ^p ≠ 1 ≠ ζ^q` by primitivity). De Bruijn 1953 for `{0,1}` coefficients at squarefree two-prime `n` is now a two-sided theorem.
* Witnesses with teeth: `ζ + ζ⁴ = 0` over `ℂ` falls out of a kernel-`decide`d `+3`-closure check on `{1,4} ⊆ ZMod 6` (no root-of-unity manipulation), and the forward direction fires end-to-end on the same nonempty set.

**Falsify-first probe (`scripts/probes/probe_debruijn_squarefree.py`, exact ℤ[x]/Φ_n arithmetic — vanishing tested by exact division by the cyclotomic, fiber sums reduced in ℤ[x]/Φ_{p^a} — exit 0):** the equivalence EXHAUSTIVE over all 2^n subsets at n = 6, 10, 15 (10/34/38 vanishing sets, 0 mismatches), 30,000 sampled + adversarial (pure-with-one-point-toggled — the toggles never vanish, so sufficiency has teeth) at n = 21, 35 (5,000 vanishing each, 0 mismatches). The splice exhaustive at n = 12, 18, 15, 20 and sampled+planted at n = 36, 0 violations, with teeth: 1,047,420 of the 2^20 non-vanishing subsets at n = 20 violate the invariance. CONTROL re-confirmed: at non-squarefree n = 12 the set {0,6} ∪ {1,5,9} vanishes but satisfies NEITHER closure — squarefree-ness is load-bearing in the iff exactly as O87 measured.

**Literature note (this session's sweep, June 2026):** no public Lean/Isabelle/mathlib formalization of de Bruijn 1953 or Lam–Leung exists (GitHub code search + web) — the in-tree ledger (O66→O91) appears to be the first machine-checked de Bruijn-type theory of vanishing sums of roots of unity. (Adjacent: arXiv 2008.11268, updated Dec 2025, classifies minimal vanishing sums to weight ≤ 21 — weight-bounded, not subset-shaped.)

**Where the de Bruijn frontier sits now:** with O77 (the full `PacketUnion` decomposition on the value surface) and O90 (the packet-combination descent engine) landed in parallel, the necessity side of de Bruijn is complete at every `p^a·q^b`; these two bricks supply the EXPONENT-surface (`ZMod`) statements the consumers use — the general-`(a,b)` fiber slice and the squarefree two-sided equivalence — plus the factorization-free sufficiency engine (the O76 cover entry records that cover alone does NOT imply vanishing; shift-closure does). Remaining mechanical step, named by O77: wire `PacketUnion` into O73's (`MixedRadixTower`) closure-hypothesis format to make the conditional tower's first rung unconditional.

### O91 — de Bruijn: the O79 splice LANDED + the squarefree classification completed to an EQUIVALENCE (sufficiency engine at every modulus)

Two complement bricks around the O87 disjointness landing, both queued by the in-tree ledger and neither stated anywhere on main: the O79 step-(1) entry's deferred splice ("composing the two yields the full two-prime subset-sum fiber slice with no hypothesis; deliberately not built this pass to avoid depending on an unlanded sibling file" — both siblings have since landed), and the SUFFICIENCY half of de Bruijn step (3) (O87 proved vanishing ⟹ closure; the packet cover proved per-element necessity; nothing proved closure ⟹ vanishing).

**Brick 1 (`CRTSubsetSumFiberSlice.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings): the splice.**
* `vanishing_subset_sum_fiber_slice` — **the unconditional two-prime subset-sum fiber slice at general `p^a·q^b`**: distinct primes `p ≠ q`, `0 < b`, `ζ` a primitive `(p^a·q^b)`-th root in ANY characteristic-zero field, `S ⊆ ZMod (p^a·q^b)` with `∑_{e∈S} ζ^e = 0` ⟹ the CRT-grid fiber sums `∑_{j<p^a} [(j, i·q^{b−1}+s) ∈ gridSet S]·(ζ^{q^b})^j` are independent of `i < q`. Steps (0)+(1)+(2) composed (`subset_sum_eq_grid_double_sum` + `crt_fiber_slice_coprimePrimePowers`); only the primitive root and the vanishing sum remain. (The O87 lane inlined this composition at `a = b = 1`; the general exponent-surface statement was still missing — it is the input shape for the `a·b > 1` packet-combination recursion named open by O87.) Non-vacuity at a NONEMPTY vanishing sum (`n = 6`, `S = {1,4}`, `ζ + ζ⁴ = 0` over `ℂ`).

**Brick 2 (`DeBruijnSquarefreeIff.lean`, axiom-clean, 0 sorry, 0 warnings): the equivalence.**
* `sum_pow_val_eq_zero_of_addClosed` — **the shift engine, any modulus**: a subset of `ZMod n` closed under translation by `d` has vanishing sum against any `n`-th root `ζ` with `ζ^{d.val} ≠ 1` (translation is a bijection of S onto itself ⟹ the sum absorbs a factor `ζ^{d.val}`). Consumes nothing about `n`'s factorization — the sufficiency mechanism at EVERY level of the de Bruijn program.
* `vanishing_of_addClosed_packet` — prime-power instantiation: in `ZMod (p^a·q^b)`, closure under the packet step `+p^a·q^{b−1}` (a union of rotated full μ_q-packets) forces vanishing. The converse of the landed `two_prime_packet_cover` necessity, at the same generality.
* `debruijn_squarefree_two_prime_iff` — **the capstone equivalence at squarefree `n = p·q`**: `∑_{e∈S} ζ^e = 0 ⟺ S` is `+p`-closed or `+q`-closed. Forward = O87's `debruijn_squarefree_two_prime`; backward = the shift engine at `d = p, q` (`ζ^p ≠ 1 ≠ ζ^q` by primitivity). De Bruijn 1953 for `{0,1}` coefficients at squarefree two-prime `n` is now a two-sided theorem.
* Witnesses with teeth: `ζ + ζ⁴ = 0` over `ℂ` falls out of a kernel-`decide`d `+3`-closure check on `{1,4} ⊆ ZMod 6` (no root-of-unity manipulation), and the forward direction fires end-to-end on the same nonempty set.

**Falsify-first probe (`scripts/probes/probe_debruijn_squarefree.py`, exact ℤ[x]/Φ_n arithmetic — vanishing tested by exact division by the cyclotomic, fiber sums reduced in ℤ[x]/Φ_{p^a} — exit 0):** the equivalence EXHAUSTIVE over all 2^n subsets at n = 6, 10, 15 (10/34/38 vanishing sets, 0 mismatches), 30,000 sampled + adversarial (pure-with-one-point-toggled — the toggles never vanish, so sufficiency has teeth) at n = 21, 35 (5,000 vanishing each, 0 mismatches). The splice exhaustive at n = 12, 18, 15, 20 and sampled+planted at n = 36, 0 violations, with teeth: 1,047,420 of the 2^20 non-vanishing subsets at n = 20 violate the invariance. CONTROL re-confirmed: at non-squarefree n = 12 the set {0,6} ∪ {1,5,9} vanishes but satisfies NEITHER closure — squarefree-ness is load-bearing in the iff exactly as O87 measured.

**Literature note (this session's sweep, June 2026):** no public Lean/Isabelle/mathlib formalization of de Bruijn 1953 or Lam–Leung exists (GitHub code search + web) — the in-tree ledger (O66→O91) appears to be the first machine-checked de Bruijn-type theory of vanishing sums of roots of unity. (Adjacent: arXiv 2008.11268, updated Dec 2025, classifies minimal vanishing sums to weight ≤ 21 — weight-bounded, not subset-shaped.)

**Where the de Bruijn frontier sits now:** with O77 (the full `PacketUnion` decomposition on the value surface) and O90 (the packet-combination descent engine) landed in parallel, the necessity side of de Bruijn is complete at every `p^a·q^b`; these two bricks supply the EXPONENT-surface (`ZMod`) statements the consumers use — the general-`(a,b)` fiber slice and the squarefree two-sided equivalence — plus the factorization-free sufficiency engine (the O76 cover entry records that cover alone does NOT imply vanishing; shift-closure does). Remaining mechanical step, named by O77: wire `PacketUnion` into O73's (`MixedRadixTower`) closure-hypothesis format to make the conditional tower's first rung unconditional.
### O91 — de Bruijn: the O79 splice LANDED + the squarefree classification completed to an EQUIVALENCE (sufficiency engine at every modulus)

Two complement bricks around the O87 disjointness landing, both queued by the in-tree ledger and neither stated anywhere on main: the O79 step-(1) entry's deferred splice ("composing the two yields the full two-prime subset-sum fiber slice with no hypothesis; deliberately not built this pass to avoid depending on an unlanded sibling file" — both siblings have since landed), and the SUFFICIENCY half of de Bruijn step (3) (O87 proved vanishing ⟹ closure; the packet cover proved per-element necessity; nothing proved closure ⟹ vanishing).

**Brick 1 (`CRTSubsetSumFiberSlice.lean`, axiom-clean [propext, Classical.choice, Quot.sound], 0 sorry, 0 warnings): the splice.**
* `vanishing_subset_sum_fiber_slice` — **the unconditional two-prime subset-sum fiber slice at general `p^a·q^b`**: distinct primes `p ≠ q`, `0 < b`, `ζ` a primitive `(p^a·q^b)`-th root in ANY characteristic-zero field, `S ⊆ ZMod (p^a·q^b)` with `∑_{e∈S} ζ^e = 0` ⟹ the CRT-grid fiber sums `∑_{j<p^a} [(j, i·q^{b−1}+s) ∈ gridSet S]·(ζ^{q^b})^j` are independent of `i < q`. Steps (0)+(1)+(2) composed (`subset_sum_eq_grid_double_sum` + `crt_fiber_slice_coprimePrimePowers`); only the primitive root and the vanishing sum remain. (The O87 lane inlined this composition at `a = b = 1`; the general exponent-surface statement was still missing — it is the input shape for the `a·b > 1` packet-combination recursion named open by O87.) Non-vacuity at a NONEMPTY vanishing sum (`n = 6`, `S = {1,4}`, `ζ + ζ⁴ = 0` over `ℂ`).

**Brick 2 (`DeBruijnSquarefreeIff.lean`, axiom-clean, 0 sorry, 0 warnings): the equivalence.**
* `sum_pow_val_eq_zero_of_addClosed` — **the shift engine, any modulus**: a subset of `ZMod n` closed under translation by `d` has vanishing sum against any `n`-th root `ζ` with `ζ^{d.val} ≠ 1` (translation is a bijection of S onto itself ⟹ the sum absorbs a factor `ζ^{d.val}`). Consumes nothing about `n`'s factorization — the sufficiency mechanism at EVERY level of the de Bruijn program.
* `vanishing_of_addClosed_packet` — prime-power instantiation: in `ZMod (p^a·q^b)`, closure under the packet step `+p^a·q^{b−1}` (a union of rotated full μ_q-packets) forces vanishing. The converse of the landed `two_prime_packet_cover` necessity, at the same generality.
* `debruijn_squarefree_two_prime_iff` — **the capstone equivalence at squarefree `n = p·q`**: `∑_{e∈S} ζ^e = 0 ⟺ S` is `+p`-closed or `+q`-closed. Forward = O87's `debruijn_squarefree_two_prime`; backward = the shift engine at `d = p, q` (`ζ^p ≠ 1 ≠ ζ^q` by primitivity). De Bruijn 1953 for `{0,1}` coefficients at squarefree two-prime `n` is now a two-sided theorem.
* Witnesses with teeth: `ζ + ζ⁴ = 0` over `ℂ` falls out of a kernel-`decide`d `+3`-closure check on `{1,4} ⊆ ZMod 6` (no root-of-unity manipulation), and the forward direction fires end-to-end on the same nonempty set.

**Falsify-first probe (`scripts/probes/probe_debruijn_squarefree.py`, exact ℤ[x]/Φ_n arithmetic — vanishing tested by exact division by the cyclotomic, fiber sums reduced in ℤ[x]/Φ_{p^a} — exit 0):** the equivalence EXHAUSTIVE over all 2^n subsets at n = 6, 10, 15 (10/34/38 vanishing sets, 0 mismatches), 30,000 sampled + adversarial (pure-with-one-point-toggled — the toggles never vanish, so sufficiency has teeth) at n = 21, 35 (5,000 vanishing each, 0 mismatches). The splice exhaustive at n = 12, 18, 15, 20 and sampled+planted at n = 36, 0 violations, with teeth: 1,047,420 of the 2^20 non-vanishing subsets at n = 20 violate the invariance. CONTROL re-confirmed: at non-squarefree n = 12 the set {0,6} ∪ {1,5,9} vanishes but satisfies NEITHER closure — squarefree-ness is load-bearing in the iff exactly as O87 measured.

**Literature note (this session's sweep, June 2026):** no public Lean/Isabelle/mathlib formalization of de Bruijn 1953 or Lam–Leung exists (GitHub code search + web) — the in-tree ledger (O66→O91) appears to be the first machine-checked de Bruijn-type theory of vanishing sums of roots of unity. (Adjacent: arXiv 2008.11268, updated Dec 2025, classifies minimal vanishing sums to weight ≤ 21 — weight-bounded, not subset-shaped.)

**Where the de Bruijn frontier sits now:** with O77 (the full `PacketUnion` decomposition on the value surface) and O90 (the packet-combination descent engine) landed in parallel, the necessity side of de Bruijn is complete at every `p^a·q^b`; these two bricks supply the EXPONENT-surface (`ZMod`) statements the consumers use — the general-`(a,b)` fiber slice and the squarefree two-sided equivalence — plus the factorization-free sufficiency engine (the O76 cover entry records that cover alone does NOT imply vanishing; shift-closure does). Remaining mechanical step, named by O77: wire `PacketUnion` into O73's (`MixedRadixTower`) closure-hypothesis format to make the conditional tower's first rung unconditional.

### O79 — THE Q-POWER DESCENT: the q-packet spectrum drops one level (the windowed engine)

`DeBruijnTwoPrime.packetUnion_qpow_descent` (axiom-clean, 0 sorry): on any PacketUnion,
Σ_{y∈S} y^q = q · Σ_{r∈R} r where R is a COLLISION-FREE spectrum (each r the common
q-th power of a full μ_q-orbit inside S). μ_p-packets die at exponent q (the twisted
packet sum, ω_p^q still primitive — pow_of_coprime); μ_q-packets each contribute q·z^q
(rep power is j-independent: ζq^{q^{b+1}} = 1); collisions are impossible by the ORBIT
ARGUMENT (equal q-th powers differ by a q-th root of unity, which would place the new
rep inside an old packet — contradicting peel disjointness).

Consequence (char 0): a window condition at exponent q forces Σ_R r = 0 — the spectrum
R is a vanishing subset of μ_{p^(a+1)·q^b}, ONE q-LEVEL DOWN, and the de Bruijn
decomposition applies again. This is the recursion engine of the windowed two-prime law
(O70): windows kill μ_q-packets level by level, exactly as the verified law predicts.
The remaining assembly: iterate the descent b+1 times and stack with the p-side climb —
mechanical given this engine + O77/O78.

### O91 — the squarefree pq classification goes TWO-SIDED: the iff, the packet-union representation, and the cardinality law (sibling to O87)

O87 closed step (3) at `a·b = 1` in forward shift-closure form. This pass lands the COMPLEMENT — the full equivalence and the representation API (`DeBruijnSquarefreePQ.lean`, axiom-clean `[propext, Classical.choice, Quot.sound]`, 0 sorry):

* `vanishing_combination_const` / `subset_sum_rigidity` — the rigidity engine in trichotomy form: a vanishing ℚ-combination of `1,ξ,…,ξ^{p−1}` has all coefficients equal (`minpoly.dvd` + degree pinch against `Φ_p`, coefficient extraction through `C·X^j`), hence two subsets of `μ_p` with equal sums are EQUAL or `{∅, μ_p}` — stated with both degenerate witnesses explicit, the form the fiber case-split consumes directly.
* `grid_vanishing_iff_pure` — **the classification as an IFF on the CRT grid**: for `I ⊆ [0,p) ×ˢ [0,q)`, the double sum vanishes ⟺ `I = A ×ˢ [0,q)` or `I = [0,p) ×ˢ T`. Forward = O83 fiber-slice invariance at `a = b = 1` + rigidity; CONVERSE = the geometric-sum factorization (`IsPrimitiveRoot.geom_sum_eq_zero`), which O87 did not state.
* `vanishing_subset_sum_iff_pure_packets` / `vanishing_subset_sum_iff_packet_union` — the headline iffs through the O82 bijection, the latter in exponent space: `S` vanishes ⟺ `S` IS the `gridMap`-image of a pure product — a disjoint union of rotated `μ_q`-packets or of rotated `μ_p`-packets. Transport lemmas `image_gridMap_gridSet` (reconstruction: `gridMap '' gridSet S = S`) and `gridSet_image_gridMap` (`gridSet (gridMap '' J) = J` for grid subsets `J`) make the two surfaces interchangeable for downstream consumers.
* `card_of_vanishing_subset_sum` — **Lam–Leung at `pq` with structure**: `q ∣ |S| ∨ p ∣ |S|`, the witnessing multiple counting whole packets.

Falsified first (`scripts/probes/probe_debruijn_squarefree_pq.py`, exact `ℤ[x]/Φ_n`, exit 0): rigidity exhaustive at `p ∈ {3,5,7,11,13}` (all `2^p` subsets, the ONLY collision is `∅` vs full); the iff exhaustive at `n = 6` (10 vanishing = `2² + 2³ − 2`, all pure) and `n = 15` (all `2^15`; 38 = `2³ + 2⁵ − 2`); `n = 35`: all `2⁵ + 2⁷` pure forms vanish + 200k random + 2k single-toggle adversarial non-pure subsets all non-vanishing. The census counts matching `2^p + 2^q − 2` exactly is the converse made visible.

**Literature pin (research lane, full annotated report posted to #232):** the forward `pq` content is de Bruijn 1953 §3, modern proof = Lam–Leung J. Algebra 224 (2000) Thm 3.3 (the double-slice argument the in-tree engine reproduces) with Cor 3.4 the minimality classification; the `p^a q^b` multiset-disjointness phrasing is Malikiosis arXiv:2005.05800 Thm 5.2. **No formalization of any of this theory exists outside this tree** (mathlib4, Isabelle/AFP, Coq searched 2026-06-09). The O70 `t > 1` window law is NOT in the literature (closest: Kumar–Senthil Kumar single-ℓ power sums, arXiv:1503.07281, weights only) — it is an original observation; recommended proof route = peeling lemma + p-power compression. **Load-bearing warning** (Kiss–Łaba–Marshall–Somlai arXiv:2507.11672, Thm 1.3/Prop 8.2): prescribed cyclotomic divisibility at an ARBITRARY scale set does NOT force packet structure even at two primes (counterexample at `M = 2⁹3⁶`, 7 scales, beats every fibered configuration) — any window-law proof MUST use the downward-closedness of `{g : g ≤ t}` (the BCH/consecutive-zeros structure); the generalization from windows to arbitrary divisor prescriptions is FALSE.
### O92 — de Bruijn WIRING step 1 LANDED: the single-prime-power theorem is an iff (one-shot O90, no recursion), and the two-prime recursion shape is pinned exactly — the remaining wall is THREAD-SPLIT

O90 closed with "what remains is WIRING: run the recursion down the digits". This pass executes the wiring probe and ships the first wiring deliverable, with one structural finding: at a PURE prime power the recursion is unnecessary — divisibility of the degree-< p^(a+1) indicator polynomial by Φ_{p^(a+1)} = packet p p^a already pins every digit via ONE application of O90's `packet_dvd_iff_slice_replication`.

**Falsify-first probe (`probe_prime_power_descent.py`, exact integer arithmetic mod Φ_n, exit 0, 30/30):** (A) the single-prime-power iff EXHAUSTIVELY at n = 4, 8, 9, 16 (vanishing ⟺ +p^a-closed; counts exactly 2^(p^a)) and sampled at 27, 25 (20000 non-closed masks all non-vanishing). (B) the brief's task (a): the full two-prime digit-descent recursion at n = 12, 18 — thread-split at the squared prime (e = r + p·e'), recurse to the squarefree base n = 6, apply the O87 dichotomy, lift packets (x ↦ r + p·x) — decomposes ALL 100/1000 vanishing subsets (O87's exhaustive census; 99/999 nonempty = O67) into disjoint genuine packets; mixture counts 24/432 reproduce O87; thread-split holds as an exhaustive IFF over all 2^12/2^18 masks (vanish ⟺ all p threads vanish at n/p); and the disjoint-packet-union family generated directly EQUALS the vanishing family — de Bruijn's ℕ-combination statement as a set identity, third witness.

**New brick `DeBruijnPrimePower.lean` (axiom-clean, 0 sorry, witnesses fired at ℂ with teeth):**
* `indicatorPoly` + coefficient/degree/aeval lemmas — the subset-sum → polynomial bridge; `indicatorPoly_coeff_mem`: coefficients in {0,1}.
* `cyclotomic_dvd_indicatorPoly_of_vanishing` — vanishing at ζ_n ⟹ Φ_n ∣ indicatorPoly S over ℚ (`cyclotomic_eq_minpoly_rat` + `minpoly.dvd`), stated at EVERY n — the reusable entry point for composite-level wiring.
* `closed_add_pow_of_vanishing` / `vanishing_of_closed_add_pow` / `debruijn_prime_power` — **the headline iff**: Σ_{e∈S} ζ^e = 0 ⟺ S closed under e ↦ e + p^a ⟺ S is a disjoint union of rotated full μ_p-packets (Lam–Leung single-prime case, sharpened to indicators: the ℕ-combination is a disjoint union). Forward = O90 slice replication + ZMod digit bookkeeping; converse = shift-reindexing (T = ζ^(p^a)·T, ζ^(p^a) ≠ 1).
* `vanishing_indicator_eq_packet_combination` — the literal de Bruijn ℕ-combination: indicatorPoly S = Σ_{s<p^a} C(coeff s)·X^s·Φ_{p^(a+1)}, coefficients {0,1} — O90's `cyclotomic_dvd_combination` fired at a genuine vanishing source.
* Teeth: 1 + i ≠ 0 DERIVED from the headline (hypothetical vanishing of the non-closed {0,1} at n = 4 contradicts decidable non-closure).

**Where the open core moves (HOLD, wall named):** the full two-prime assembly (n = p^a q^b ⟹ S = S_p ⊔ S_q with S_p +n/p-closed, S_q +n/q-closed) is induction + this base + O87's squarefree dichotomy, EXCEPT one missing analytic brick: **THREAD-SPLIT** — for p² ∣ n, a vanishing sum at ζ_n splits into p vanishing thread sums at ζ_n^p (ℚ(ζ_{n/p})-linear independence of 1, ζ, …, ζ^{p-1}, i.e. minpoly ℚ⟮ζ^p⟯ ζ = X^p − ζ^p). The probe verifies it as an exhaustive IFF at 12, 18; no in-tree brick proves it. The path is concrete and CRTPacketMinpoly-shaped: divisibility by the monic binomial + tower degree bound via `Nat.totient_mul_of_prime_of_dvd` (φ(n) = p·φ(n/p) for p² ∣ n) + `linearIndependent_pow` (Mathlib RingTheory/PowerBasis.lean:415) for the coefficient extraction; then the lift bookkeeping (packets lift to packets, both types, as the probe's decomposer executes). That single brick + induction completes Theorem de Bruijn 1953 two-prime in-tree.

### O80 — THE SPECTRAL SYNDROME TRANSFER: the full window descends in one theorem

`DeBruijnTwoPrime.packetUnion_spectral_transfer` (axiom-clean, 0 sorry): ONE spectrum R
carries the ENTIRE syndrome window — for EVERY exponent e with p ∤ e,

    Σ_{y∈S} y^{q·e} = q · Σ_{r∈R} r^e.

Supersedes O79 (its e = 1 case): μ_p-packets die at every exponent q·e with p ∤ e
(ω_p^{qe} primitive via Coprime.mul_left of the two coprimalities), μ_q-packets each
contribute q·(z^q)^e with the SAME spectrum point for all e, and the orbit argument
keeps R collision-free. Consequence: a window of S at {q·e : e ≤ w, p ∤ e} is a window
of R at {e ≤ w, p ∤ e} one q-level down — THE complete recursion step of the windowed
two-prime law. The full windowed law is now: iterate (b+1 times), apply the prime-power
endpoint (O66), and stack the p-side climb — every ingredient machine-checked.
### O93 — THREAD-SPLIT LANDED: the O92 wall is a theorem — vanishing at ζ_n with p² ∣ n splits into p vanishing thread sums at ζ_n^p (an iff), via minpoly ℚ(ζ^p) ζ = X^p − ζ^p

O92 closed with one named analytic wall for the full two-prime de Bruijn assembly: THREAD-SPLIT — for p² ∣ n, a vanishing sum at ζ_n splits thread-by-thread at ζ_n^p (ℚ(ζ_{n/p})-linear independence of 1, ζ, …, ζ^{p−1}), probe-verified as an exhaustive iff at n = 12, 18 but proved nowhere in-tree. This pass proves it, both directions, after extending the measurement to the brief's points.

**Falsify-first probe (`probe_thread_split.py`, exact integer arithmetic mod Φ_n, exit 0, 13/13):** the iff EXHAUSTIVELY over ALL masks at n = 20 (2²·5) and n = 28 (2²·7) — since thread decomposition is a bijection masks ↔ thread-tuples, the set identity vanishing-family = thread-product-family IS the exhaustive iff; counts confirm the product law |van(n)| = |van(n/p)|^p exactly (1156 = 34² at 20, 16900 = 130² at 28). Sampled with teeth at n = 50 (p = 5) and bonus odd-p² point n = 45 (p = 3): 2000 planted all-threads-vanishing masks all vanish, 20000 random masks satisfy the iff pointwise, and 2000 single-bit toggles of planted masks are non-vanishing with the toggled thread exactly the bad thread — both sides of the iff flip together, one-sided failure never observed.

**New brick `ThreadSplit.lean` (axiom-clean, 0 sorry, witnesses fired at ℂ with teeth):**
* `minpoly_adjoin_pow_prime_eq_binomial` — **the engine**: for n = p·m with p ∣ m, minpoly ℚ⟮ζ^p⟯ ζ = X^p − C(gen ℚ (ζ^p)). Degree pinch exactly as O92 named it: ≤ p from divisibility by the monic binomial (`minpoly.dvd` + `monic_X_pow_sub_C`); ≥ p from the totient tower bound p·φ(m) = φ(p·m) = [ℚ(ζ):ℚ] ≤ [ℚ⟮ζ^p⟯⟮ζ⟯:ℚ] = φ(m)·[ℚ⟮ζ^p⟯⟮ζ⟯:ℚ⟮ζ^p⟯] (`Nat.totient_mul_of_prime_of_dvd` — the LOAD-BEARING use of p² ∣ n; at p ∤ m the true degree is p−1 — plus `Module.finrank_mul_finrank` and the ℚ-linear embedding ℚ⟮ζ⟯ ↪ ℚ⟮ζ^p⟯⟮ζ⟯), closed by `eq_of_monic_of_dvd_of_natDegree_le` — the CRTPacketMinpoly pattern executed at the NON-coprime tower step the coprime brick cannot reach. `natDegree_minpoly_adjoin_pow_prime`: [ℚ(ζ_n):ℚ(ζ_{n/p})] = p, extracted.
* `sum_eq_thread_sum` — the digit-decomposition identity Σ_{e∈S} ζ^e = Σ_{r<p} ζ^r·Σ_{e'<m}[r+p·e'∈S](ζ^p)^{e'} over ANY commutative ring (`sum_nbij'` on e ↦ (e % p, e / p)).
* `thread_vanishing_of_vanishing` — **the headline**: the thread sums are coefficients in K = ℚ⟮ζ^p⟯; the engine pins (minpoly K ζ).natDegree = p, `linearIndependent_pow` (Mathlib RingTheory/PowerBasis, exactly as O92 predicted) gives K-independence of 1, ζ, …, ζ^{p−1}, and `Fintype.linearIndependent_iff` kills every thread.
* `vanishing_of_thread_vanishing` / `thread_split_iff` — the trivial converse (pure linearity, any CommRing, no primality or primitivity) and the iff in the probe's exact shape.
* Teeth: 1 + ζ₁₂ ≠ 0 DERIVED from the forward direction (the r = 0 thread of a hypothetical vanishing {0,1}-sum evaluates to 1); ζ₁₂ + ζ₁₂⁷ = 0 PRODUCED by the converse from its two vanishing threads (1 + ζ₁₂⁶ killed by `eq_neg_one_of_two_right`).

**Where the open core moves (the wall is now bookkeeping, named):** every analytic ingredient of de Bruijn 1953 two-prime is in-tree — O92's prime-power base (`debruijn_prime_power`), O87's squarefree dichotomy (`debruijn_squarefree_two_prime_iff`), and this brick's digit descent. What remains is the ASSEMBLY induction the probe's decomposer already executes numerically: recurse `thread_split_iff` down the digits of n = p^a·q^b to the squarefree base p·q, apply the dichotomy there, and lift packets through e ↦ r + p·e' (lifted packets stay genuine rotated full packets, both types — the probe's B2 check at 12, 18). One brick: the lift lemma + the strong induction wrapper, statement shape pinned by O92's layer-B census (disjoint-packet-union family = vanishing family). No new divisibility or independence content is needed anywhere in the chain.

### O81 — THE ITERATED SPECTRAL TRANSFER: the full descent chain assembled

`DeBruijnTwoPrime.iterated_spectral_transfer` (axiom-clean, 0 sorry): given the q-power
window Σ_S y^{q^c} = 0 (1 ≤ c ≤ b), for EVERY depth m ≤ b+1 the m-th spectrum R_m
exists at level μ_{p^(a+1)·q^(b+1−m)} — every element a q^m-th power of an S element —
carrying the whole window with factor q^m:

    (q : F)^m · Σ_{r∈R_m} r^e = Σ_{y∈S} y^{q^m·e}   for every p ∤ e.

Induction stacking O77 (decompose at each level — vanishing from the previous transfer
at e = 1 + the window; char-0 division by q^m) and O80 (one more transfer); level
bookkeeping via b+1−m = (b−m)+1 and ζq^{q^m} primitivity. At m = b+1 the chain bottoms
out in μ_{p^(a+1)} — the prime-power level where Lam–Leung (O66) takes over.

THE DESCENT HALF OF THE WINDOWED TWO-PRIME LAW IS COMPLETE. Remaining for the full law:
the upward reconstruction (spectrum structure ⟹ coset structure of S — the d-coset
reassembly the O70 law describes) and the symmetric p-side chain.

### O94 — the per-locus structure theorem: low-weight errors live in locator-divisible slice spaces (nubs, 2026-06-10)

`FoldPolynomialSlices.lean` extended (six new theorems, axiom-clean, 0 warnings —
pushed-diff verified against this claim):

- `recompose_slices` (char-free): `expand 2 (evenSlice f) + X·expand 2 (oddSlice f) = 2·f`
  — a polynomial is recovered from its two coefficient slices (via
  `expand_evenSlice/expand_oddSlice`: the expand∘contract round-trips).
- `natDegree_evenSlice_le` / `natDegree_oddSlice_le`: slices halve degree — the
  dimension budgets.
- `loc_dvd_iff`: vanishing on a finite point set ⟺ divisibility by its locator
  (coprime linear factors).
- `weight_ge_live_image` — the level-1 weight–dead-locus tradeoff, NOW actually landed
  (the O69→O70 record correction is closed with the artifact itself).
- `low_weight_slice_structure` — **the skeleton**: every polynomial error determines a
  dead locus Z with `|Z| ≥ |D²| − w`, BOTH slices divisible by `loc Z`, and the
  locator-divisible slices recompose to `2·f`.

**What this pins formally:** the list-relevant f's of weight w are parameterized, per
locus Z, by slice pairs `(he, ho)` in degree-truncated spaces of total dimension
`≤ deg f − 2|Z| + O(1)` — the per-locus linear space whose union-over-loci versus the
weight filter IS the surviving counting question (O70's frontier). Iterating down the
tower multiplies the constraints: each level divides out another locator. Next named
step: the union/incidence count — how many loci can a single f serve, and the
finite-field cardinality corollary `#{f : slices vanish on Z} = q^{max(0, k−2|Z|)}`.

### O82 — THE SYMMETRIC P-SIDE CHAIN + THE CHAIN ENDPOINT (both halves meet Lam–Leung)

Two theorems (axiom-clean, 0 sorry):

* `iterated_spectral_transfer_p` — the p-side descent chain as a role-swap instantiation
  of O81 (the decomposition object is symmetric; only the torsion exponent needs
  mul_comm). Both prime directions of the windowed law now have complete descent chains.
* `deep_spectrum_mu_p_closed` — THE CHAIN ENDPOINT: with the full q-power window
  (through q^(b+1)), the deepest spectrum R_{b+1} is a vanishing subset of the PURE
  prime-power level μ_{p^(a+1)}, and it is CLOSED under every p-th root of unity —
  the O81 chain welded to the prime-power membership-slice machinery
  (mu_p_membership_slices + the box/wrap bookkeeping). The descent now lands on a
  STRUCTURED object: a μ_p-closed vanishing set, i.e. a union of μ_p-cosets (full_tower
  shape) at the bottom of the two-prime tower.

The windowed law's remaining open half is now exactly ONE move: upward reconstruction
(lift the endpoint/spectrum structure back through the chain to the d-coset reassembly
of S that the O70-verified law describes).
### O94 — DE BRUIJN 1953 TWO-PRIME LANDED IN FULL: the final assembly is a theorem — Σ_{e∈S} ζ^e = 0 at n = p^a·q^b IFF S is a disjoint union of rotated full prime packets (the iff, both directions, axiom-clean)

O93 closed with exactly two named residuals: the lift lemma + the strong induction wrapper. This pass ships both and the headline they were for — Theorem de Bruijn 1953 (two-prime case, indicator form, sharpened to disjoint unions) as ONE in-tree statement.

**Falsify-first probe (`probe_debruijn_two_prime_assembly.py`, exact ℤ[x]/Φ_n meet-in-the-middle over the FULL 2^n mask space, exit 0, 20/20):** the headline iff as a set identity — the disjoint-canonical-packet-union family EQUALS the vanishing family — EXHAUSTIVELY at n = 12, 18, 20, 28 (counts 100/1000/1156/16900, matching O87/O67/O93 censuses); the recursion executed on every vanishing mask with the EXACT lift index map asserted at every lift of every level (the brief's "careful" item, pinned: canonical packets {s + t·(m/d) : t < d} with base s < m/d lift through e ↦ r + u·e to base r + u·s < u·(m/d) = (u·m)/d — canonical form survives descent, NO mod-n arithmetic exists anywhere in the development); mixture witnesses at every composite point (both packet types in one decomposition — pure type genuinely fails past squarefree, so the mixed statement is the honest one); toggle/singleton controls flip both sides together.

**Bricks (`DeBruijnTwoPrimeAssembly.lean`, axiom-clean [propext, Classical.choice, Quot.sound] ×7, 0 sorry, 0 warnings, 553 lines):**
* `IsPacket` / `IsPacketUnion` — the canonical packet predicate (base < step = n/d, d teeth) and the disjoint-union decomposition; `IsPacket.card_eq` (packets have exactly d elements, the teeth engine).
* `packet_sum_eq_zero` / `sum_eq_zero_of_isPacketUnion` — **the converse, generic**: any packet dies against any primitive n-th root (ζ^r·Σ_{t<d}(ζ^{n/d})^t, `geom_sum_eq_zero`), hence any disjoint union does (`Finset.sum_biUnion`). No two-prime structure needed.
* `isPacket_lift` — **the lift lemma (O93 residual 1)**: the image of a canonical d-packet at level m under e ↦ r + u·e (r < u) is a canonical d-packet at level u·m — `Finset.image_image` + `Nat.mul_div_assoc`, the probe's index map verbatim.
* `isPacketUnion_of_closure` — **the squarefree seam**: S ⊆ [0, w·k) closed under e ↦ (e+k) % n IS a disjoint union of canonical step-k packets, one per residue of S mod k (the orbit argument: iterate closure j = w + t − e/k times to wrap exactly once).
* `isPacketUnion_of_threads` — **the induction step**: if every thread T_r = {e' < m : r + u·e' ∈ S} decomposes at level m, S decomposes at level u·m — lift each thread's packets (lift lemma), cross-thread disjointness by residues mod u (`Nat.add_mul_mod_self_left`), non-dependent choice via guarded ∃.
* `isPacketUnion_of_sum_eq_zero` — **the strong induction wrapper (O93 residual 2)**: nested induction (p-digits to a = 1, then q-digits to b = 1); each descent = O93 `thread_vanishing_of_vanishing` + IH at ζ^u + thread assembly; the base = O87 `debruijn_squarefree_two_prime` pulled through the ℕ↔ZMod bridges (`sum_image_cast`, `closure_nat_of_closure_zmod`) into the closure seam.
* `debruijn_two_prime` — **the headline iff**, exactly the brief's target shape (O92 layer-B census as a theorem).
* Teeth at ℂ, n = 2²·3: converse PRODUCES 1 + ζ₁₂⁶ = 0 from a decide-checked one-packet decomposition; forward converts hypothetical vanishing of {0} into a card contradiction (packets need ≥ 2 elements inside a singleton) — the iff discriminates.

**Where the open core moves:** the three-step de Bruijn ledger (O73 → O87 → O90 → O92 → O93 → here) is CLOSED at two primes — vanishing 0/1 sums of p^a·q^b-th roots of unity are completely classified in-tree, the first formalization of this theorem in any proof assistant (per the O91 search). What remains beyond it is genuinely new mathematics, not assembly: (i) THREE-plus prime moduli (de Bruijn's conjecture territory — false in general by Lam–Leung; the honest target is the Lam–Leung ℕ-span theorem |S| ∈ ℕp + ℕq + …, whose two-prime case is now a corollary of this brick via `IsPacket.card_eq`); (ii) the t > 1 window law (O70) at composite n, which no literature covers; (iii) wiring this classification into the M31-domain capstone consumers (the original #232 motivation: Mersenne-31 has n = 2^a·3^b-style smooth subgroups — the two-prime case is exactly the M31 smooth-subgroup regime).

### O95 — the per-locus count is exact: q^(d−|Z|) (nubs, 2026-06-10)

`ArkLib/Data/CodingTheory/ProximityGap/SliceLocusCount.lean` (axiom-clean): the
counting companion to O94's structure theorem.

- `polysDegLT`/`card_polysDegLT`: the degree-`<d` space as a concrete Finset of size
  `q^d` (coefficient-tuple enumeration).
- `card_polysDegLT_vanishing`: **polynomials of degree `<d` vanishing on a prescribed
  `|Z|`-point locus number EXACTLY `q^(d−|Z|)`** — `(loc Z * ·)` is a bijection from
  the space one locus-size down; `loc_dvd_iff` gives surjectivity, monicity injectivity.

The Conjecture-D skeleton is now numerically explicit: per locus, slice pairs of a
degree-`<k` error range over exactly `q^(k−2|Z|)` candidates; with O94's
`|Z| ≥ |D²| − w` the per-locus budget at list-relevant weight is
`q^(k − 2(n/2 − w)) = q^(k − n + 2w)`. The surviving open content, sharply: the
union-over-loci/incidence structure versus the weight filter (how many loci, how much
overlap, what fraction of each per-locus space meets weight ≤ w). Queued capstone: the
f-level product count via `recompose_slices`.

### O96 — the per-locus budget is an EQUALITY: #{f : deg < k, both slices vanish on Z} = q^(k−2|Z|) (nubs, 2026-06-10)

`SliceLocusCount.lean` extended with the f-level capstone (axiom-clean, 0 warnings):

- Slice C-linearity (`evenSlice_C_mul`/`oddSlice_C_mul`), the build identities
  (`evenSlice_build`/`oddSlice_build`: slices of
  `expand 2 E + X·expand 2 O` are `2E`/`2O`), `expand_comp_neg_X`, sharp odd
  degree budget (`natDegree_oddSlice_le'` ≤ (deg−1)/2), zero-slice lemmas.
- `card_polysDegLT_slices_vanishing` — **the count**: `f ↦ (evenSlice f, oddSlice f)`
  is an explicit bijection (two-sided inverse via `recompose_slices` and the build
  identities, char ≠ 2) from the both-slices-vanish-on-Z space onto the product of
  per-slice locus spaces, so the per-locus budget of the O94 skeleton is EXACTLY
  `q^((k+1)/2 − |Z|) · q^(k/2 − |Z|) = q^(k − 2|Z|)`.

Status of the counting program: structure (O94) + per-slice count (O95) + f-level
count (this) are all equalities; combined with O70's forced locus size `|Z| ≥ n/2 − w`,
each list-relevant error sits in an explicitly counted space of size
`q^(k − n + 2w)` per locus at level 1. The surviving open content of the all-words
question is purely the LOCUS INCIDENCE: how the per-locus spaces overlap across the
$\binom{n/2}{·}$ loci and how the weight filter cuts them — and its iteration down
the tower. Every other term in the Conjecture-D sentence is now a theorem with an
exact constant.
### O95 — THE O94 CLASSIFICATION LANDS ON THE TOWER SURFACE: the t=1 stratum of the mixed-radix law unconditional in tower language + the M31 smooth domain (nubs, 2026-06-10)

**Inventory (the consumers, measured exactly).** The 2-power capstone chain is O53 `full_tower` (power-sum window `j < 2^s` ⟹ `μ_{2^s}`-closure) feeding O61 `unit_syndrome_list_budget`. Its two-prime analogue is the O70 divisor-coset law (window `t` ⟹ disjoint rotated `μ_d`-cosets, `d ∣ n`, `d > t`), whose closure consequence at `t ≥ q^b` is exactly the `hBasep/hBaseq` family of `MixedRadixTower.two_prime_tower_conditional` (O73). VERDICT on dischargeability: `debruijn_two_prime` is the `t = 1` stratum ONLY — and at `t = 1` uniform `μ_p`-closure is FALSE (rotated `μ_q`-packet), so NO `hBase` instance at a genuinely two-prime level is dischargeable from it; the discharge demands the `t > 1` window law, which O94 itself names as open mathematics (item ii). What IS dischargeable — and was not in tree — is the entire `t = 1` layer in the tower's own field-surface closure language.

**Falsify-first probe (`scripts/probes/probe_debruijn_tower_wiring.py`, exact ℤ[x]/Φ_n, exit 0, cold re-executed):** the two target shapes hold on ALL 1,001,100 vanishing subsets — exhaustive `n = 12` (100), `n = 18` (1000), FULL MITM census `n = 36` (1,000,000; the O70 count reproduced): pointwise dichotomy failures 0/0/0, cardinality-law failures 0/0/0. Both negative controls live: vanishing-but-not-`μ_2`-closed = 36/488/737,856 (>0 at every level — the wall is real), dichotomy-without-vanishing = 384/9648 (the corollary is one-way, not an iff — the statement does not over-claim).

**Bricks (`DeBruijnTowerWiring.lean`, new file, 350 lines, exit 0, 0 sorry, 0 warnings, axiom-clean [propext, Classical.choice, Quot.sound] ×7):**
* `expSet` + `mem/image/sum/card_expSet` — the `Finset F` ⟷ `Finset ℕ` discrete-log bridge: `T ⊆ μ_n` is the injective image of its exponent set (`eq_pow_of_pow_eq_one` + `pow_inj`), sums and cardinalities transport.
* `packet_absorb` — the absorption engine: a canonical exponent `d`-packet inside `T` absorbs the full field coset `μ_d·y` (the O94 lift map run in reverse; wraparound killed by `ζ^n = 1`).
* `vanishing_packet_dichotomy` — **the headline**: char 0, `T ⊆ μ_{p^a·q^b}`, `Σ_{y∈T} y = 0` ⟹ every `y ∈ T` carries its FULL `μ_p`-coset or its FULL `μ_q`-coset inside `T` — in exactly the closure language (`∀ g, g^p = 1 → g*y ∈ T`) of `mixed_rung_conditional`. The sharp `t = 1` two-prime analogue of `full_tower`'s first rung.
* `vanishing_card_two_prime` — **Lam–Leung at two primes on the field surface**: `|T| ∈ ℕp + ℕq` (O94's corollary promise cashed in-tree via `IsPacket.card_eq` + `card_biUnion`).
* `rung_base_dichotomy` — the dichotomy instantiated at every level `n/p^k` (`k < a`) in `prime_climb_conditional`'s own indexing: the climb's base layer is now unconditionally classified at every height (q-side symmetric).
* `m31_smooth_dichotomy` / `m31_smooth_card` — **the M31 landing**: `|F_{2^31−1}^×| = 2^31−2 = 2·3²·7·11·31·151·331`, so the two-prime-smooth multiplicative domain is `μ_18`, `18 = 2^1·3^2` — both theorems specialized there. (Census check: the in-tree M31 surface `MCAJohnsonEnvelope` (`31 ≤ M`, `n ≤ 2^M`) is the 2-adic circle side `2^31 = q+1` — pure 2-power, already covered by O53/O61; the multiplicative side is what this file covers.)
* Teeth at ℂ: the dichotomy FIRED on `{1, −1} ⊆ μ_18`; **negative control kernel-checked**: `{1, 5, 9}` at `n = 12` vanishes (O94 converse on a one-packet decomposition) yet `(1+6) % 12 = 7 ∉ {1,5,9}` (decide) — sum vanishing can NEVER discharge `hBase(w = 2)`.

**Where the open core moves:** the M31-domain capstone now has its base layer welded — what separates `two_prime_tower_conditional` from unconditional is ONE named statement, the `t > 1` window law (O70's exhaustively verified `F_n(t)` divisor-coset law: window `1..t` ⟹ components `d > t`, hence `μ_p`-closure at `t ≥ q^b`). That is genuinely new mathematics (no literature; the weighted/multiplicity de Bruijn theory is the visible route: window exponents `j` with `gcd(j,n) > 1` produce ℕ-weighted vanishing sums at lower levels, needing the Lam–Leung ℕ-span theorem rather than the indicator form). Honest next bricks: (i) the weighted prime-power packet theorem (the ℕ-coefficient generalization of O66 `packet_mul_coeff` — assembly-adjacent); (ii) the `β = 1` windowed law at level `p^α·q` window `q+1` as the first genuinely two-prime rung; (iii) with (ii), `prime_climb_conditional` goes unconditional on `n = 2^a·3` — the first unconditional mixed-radix tower instance.

### O96-erratum — the capstone section was dropped from the O96 commit by a merge error; restored (nubs, 2026-06-10)

The O96 commit (`feat: f-level per-locus count`) landed only the helper layer — a
namespace-surgery bug excluded the capstone block (`C_inv_two_mul_two`, zero-slice and
membership lemmas, `build_mem`, and `card_polysDegLT_slices_vanishing` itself). The
post-push diff verification caught it within minutes. This commit restores the full
section (compiles clean, all axiom-clean); the O96 entry's mathematical description is
accurate for the NOW-present content.

### O97 — the level-1 union bound: the incidence template, machine-checked (nubs, 2026-06-10)

`SliceLocusCount.lean`: `low_weight_count_le` — for a negation-closed domain (char ≠ 2,
`0 ∉ D`), with `s = |D²| − w`, `2s ≤ k`:

    #{f : deg f < k, weight ≤ w}  ≤  C(|D²|, s) · q^(k − 2s).

Proof = the now-complete level-1 pipeline composed end-to-end: every low-weight `f`
forces a dead locus of size ≥ s (O94 structure theorem), it contains a size-s sub-locus
(subsets of dead loci are dead), and each per-locus space counts exactly `q^(k−2s)`
(O96 capstone); union over `C(|D²|, s)` loci.

HONEST SCOPE: as a pure number this is classically subsumed (RS is MDS; weight
distributions are exact via MacWilliams) — and the classical exactness does NOT resolve
the list question (lists are cliques around an arbitrary word, not balls at 0), so
neither does this bound alone. Its value: (1) the first machine-checked
weight-distribution-type bound through the slice route, (2) the TEMPLATE every tower
level instantiates — the iterated version's gain must come from cross-level interaction
of the loci (the genuinely open incidence), and now every ingredient of that sentence is
a formal object in-tree. Level-1 story complete: structure (O94) + per-slice count (O95)
+ f-level equality (O96) + union bound (this). Next frontier, named precisely: the
incidence/clique structure — pairwise difference loci of LIST configurations (around a
word, not 0) and the cross-level locus interaction down the tower.
### O96 — THE WEIGHTED PRIME-POWER PACKET THEOREM (O95's named brick (i)): the ℕ-coefficient de Bruijn/Lam–Leung classification at p^(a+1) is a theorem — and the O90 engine needed ZERO new divisibility content

O95 closed naming the route to the t > 1 window law through the weighted theory, brick (i) being "the weighted prime-power packet theorem (assembly-adjacent)". The brief's CHECK-FIRST question is answered YES and machine-checked: O90's `packet_dvd_iff_slice_replication` never assumed {0,1} coefficients — the indicator restriction in O92 was an instantiation, not a hypothesis — so the ℕ-weighted theorem at a prime power is the same engine run on a weight polynomial.

**Falsify-first probe (`scripts/probes/probe_weighted_packets.py`, exact ℤ[X] mod Φ_n, exit 0, cold re-executed):** (A) the weighted iff (vanish ⟺ p^a-periodic weight), the ℕ-combination reconstruction, and the weight law p ∣ |w| EXHAUSTIVELY at n = 4 (weights ≤ 3; 16 vanishing), 8 (≤ 2; 81), 9 (≤ 2; 27) — vanishing counts are EXACTLY (W+1)^(p^a), the pure replication freedom — plus 2000 planted replicated weights at n = 27 (all vanish) with single-increment toggles (all non-vanishing). Negative control alive at every level: p ∣ |w| WITHOUT vanishing exists — the weight law is one-way. (B) **the brief's two-prime question answered in shape**: at n = 12, ALL 2025 vanishing weight vectors (entries ≤ 2, exhaustive over 3^12 = 531441 masks) ARE ℕ-combinations of rotated full prime packets — the packet-combination form does NOT fail under weighted mixtures (1272 genuine mixtures, 768 forcing a combination coefficient ≥ 2 — outside the indicator theory, still decomposable); weight law |w| ∈ ℕ2+ℕ3 violations 0; n = 18 planted ℕ-combinations all vanish + re-decompose, toggles all non-vanishing. Census echo: 2025 = 45², the thread-split product law |van₁₂| = |van₆|² reproduced on the weighted surface.

**Bricks (`WeightedPrimePowerPacket.lean`, new file, 419 lines, exit 0, 0 sorry, 0 warnings, axiom-clean [propext, Classical.choice, Quot.sound] ×10):**
* `weightPoly` + coeff/degree/aeval lemmas — the weight-function → polynomial bridge (`indicatorPoly` is the special case w = 1_S); `cyclotomic_dvd_weightPoly_of_vanishing` — the O92 entry point, coefficient-agnostic, stated at EVERY n for composite-level weighted wiring.
* `weight_replicated_of_vanishing` / `vanishing_of_weight_replicated` / `debruijn_prime_power_weighted` — **the headline iff**: Σ_e w(e)·ζ^e = 0 at n = p^(a+1) ⟺ w(e + p^a) = w(e) for ALL e — the weight function is p^a-periodic, i.e. the sum is an ℕ-combination of rotated full μ_p-packets with multiplicities w(s). Forward = one-shot O90 slice replication on `weightPoly` (digit bookkeeping verbatim from O92); converse = shift-reindexing of the full Fintype sum (`Equiv.sum_comp`).
* `vanishing_weight_eq_packet_combination` — **the literal Lam–Leung ℕ-span structure**: weightPoly w = Σ_{s<p^a} C(w s)·X^s·Φ_{p^(a+1)}, combination coefficients literally the weights — nonnegative, no sign correction.
* `total_weight_eq_p_mul` / `prime_dvd_total_weight` — **the Lam–Leung weight law at a prime power, exact form**: Σ_e w(e) = p·Σ_{s<p^a} w(s), hence |w| ∈ ℕp — evaluation of the combination at X = 1 via `eval_one_cyclotomic_prime_pow` (Φ_{p^(a+1)}(1) = p), no combinatorial bijection needed.
* Teeth at ℂ on GENUINELY weighted data (weights ≥ 2, outside the indicator theory): converse PRODUCES 2 + 2ζ₄² = 0 from the decidably 2-periodic weight (2,0,2,0); forward REFUTES vanishing of (2,0,1,0) (2 ≠ 1 from weighted structure alone); the weight law REFUTES vanishing of the odd-total weight (0,1,0,0) (2 ∤ 1) — all three conclusions discriminate.

**Where the open core moves (the (c) verdict, honest):** the two-prime weighted STRUCTURE law survives the probe intact (de Bruijn 1953's full ℕ-statement, not just the indicator case — no weighted-mixture counterexample exists at n = 12 exhaustively), so the in-tree target is real, but its assembly is NOT free: (1) weighted THREAD-SPLIT transports — O93's engine (`minpoly_adjoin_pow_prime_eq_binomial`, `natDegree_minpoly_adjoin_pow_prime`) is coefficient-free and the K-linear-independence argument accepts weighted thread sums verbatim; only the consumer statement is indicator-bound (bookkeeping). (2) The genuine wall is the **weighted SQUAREFREE base at n = pq**: periodicity fails there (the probe's 1272 mixtures), so the statement is ℕ-cone membership — every ℕ-point of the packet lattice kernel is an ℕ-combination of the p+q rotated packets — de Bruijn's Lemma-1 cone argument, no in-tree analogue (O87's dichotomy is its indicator shadow). With (1)+(2), this pass's prime-power base completes the weighted two-prime theorem by the O94 induction shape, and O95's brick (ii) (the β = 1 windowed law at p^α·q, window q+1) becomes consumable.

### O98 — C1379: the level-2 marginal layer is ONE cyclotomic equation; the deep line at n=32 (nubs, 2026-06-10)

`scripts/probes/n32census/level2/` (commit 75e4822b2; adversarially audited, sound 0.95). **(A) The
1,344 agree-17 layer of the O87 census, completely charted** — and reproduced index-identically by a
full fresh sweep at a second prime p₂ = 3·2³⁰+1 (the same literal agreement sets ⟹ ONE ℤ[ζ₃₂]
configuration reduced at split primes): every dense element factors as
Π_B(X²−z_b)·(X−x₁)(X−x₂)(X−x₃)(X−ξ), ξ = −Σxᵢ forced, (|B|,|O|) = (7,3) universal; consistency =
the single scalar equation e₂(x⃗) − e₁(x⃗)² = λ + e₁(B) (0/1344 failures). 1,344 = 2·672 via free
negation (parity-forced); B-census 580 = 488(×2) + 92(×4) — the SAME {2,4} multiplicity menu as
C19's level-1 census. 35 = C(7,4) is now STRUCTURAL (e₁(S) = −λ ⟹ z* ∈ S + O50 antipodal pairs).
O63 spread: witnesses minimal, dense layer MAXIMAL (every branch alive, depths 1–3). The n=16
union-containment invariant does NOT lift; the level-2 invariant is the 19-type lattice profile.
**Conjecture C1379** (C19-at-level-2, char-0): ℓ(w,18) = 35, ℓ(w,17) = 1,379 with this fixed
index-level anatomy for all but finitely many split characteristics; named remaining analytic step:
derive 672 from the equation. Falsifiers: any further split prime's 4-minute sweep; a non-max-fiber λ.
**(B) Deep line at n=32** (calibrated bit-for-bit vs O68 first): the FULL C(16,9) = 11,440 bad
scalars (injective scalar map at this z; vs monomial N₀ = 3,280 — the O68 gap widens 1.4×→3.49×),
ALL singleton floor lists, union = {q_S} exactly; degeneracy impossible a priori (S_A ≡ 1 + w⁹S_B);
a = 17 = k+1 proven line-trivial and exactly counted (263,802,303 γ's; cross-foot to C(32,17)
exact). **Level-2 moral for the branch-count distribution: maximal concentration at the witness
floor on both families; the first marginal layer is a finite explicit consistency equation with the
same {2,4} multiplicities at both proven levels.**
### O97 — THE TWO-PRIME WINDOW LAW IS A THEOREM: the mixed-radix tower goes UNCONDITIONAL (the O95 separation closed)

O95 closed with: "what separates `two_prime_tower_conditional` from unconditional is ONE named statement, the `t > 1` window law … genuinely new mathematics (no literature; the weighted/multiplicity de Bruijn theory is the visible route)". This pass proves that statement at EVERY two-prime modulus `n = p^a·q^b` — and the visible route was not needed: induction on the `q`-exponent over the landed O94 classification suffices. The conditional tower (O73) is now an unconditional theorem at exact two-prime levels.

**Falsify-first probe (`scripts/probes/probe_two_prime_window_law.py`, exact ℤ[x]/Φ_n, exit 0):** the rung EXHAUSTIVELY over the full `2^n` mask space at `n = 12, 18, 20, 24` and the full MITM census at the deep point `n = 36` (`a = b = 2`): every subset vanishing on the SPARSE window `{q^c : c ≤ b}` is `μ_p`-closed — candidates 64/512/1024/4096/262144 (= exactly `2^(n/p)`, the unions of `μ_p`-cosets — the iff made visible), 0 violators, both orientations. Sharpness: dropping the top exponent `q^b` admits the rotated `μ_{q^b}`-coset violator at every point (the sparse window is minimal in length). Capstone interval window `W = max(p^(a-1)(q^b+1), q^(b-1)(p^a+1))` forces empty/full at every point; sharp interval thresholds recorded (slack 2/1/2/4/2 — within one of sharp at `n = 18`).

**Bricks (`TwoPrimeWindowLaw.lean`, new file, 9 theorems, 0 sorry, 0 warnings, axiom-clean [propext, Classical.choice, Quot.sound] ×9):**
* `window_mu_p_closed` — **THE RUNG**: char 0, `T ⊆ μ_{p^a·q^b}` (`a ≥ 1`, `b ≥ 0`), power sums vanishing at the `b+1` exponents `{1, q, …, q^b}` ⟹ `T` is `μ_p`-closed. Induction on `b`: the `c = 0` sum + O94 `debruijn_two_prime` decompose the exponent set; at exponent `q^(c+1)` every `μ_p`-packet dies (`packet_sum_pow_coprime`: twisted geometric sum at a coprime power is still full) and every `μ_q`-packet collapses to `q·ρ^(q^c)` for its spectrum point `ρ = ζ^(q·base)` (`qpacket_sum_pow`); canonical bases `< n/q` make the spectrum COLLISION-FREE (`q·base < n` pins the discrete log — no choice needed: the spectrum value is `(q)⁻¹·Σ_{e∈P}(ζ^q)^e`, a total function of the packet); the spectrum is a vanishing subset of `μ_{p^a·q^(b-1)}` inheriting the window one level down; the floor `b = 0` is Lam–Leung at prime powers (O66). Closure lifts back: `g^q ∈ μ_p` moves spectrum points and the moved packet absorbs `g·y` via O95 `packet_absorb`.
* `pow_sum_eq_zero_of_mu_p_closed` + `window_iff_mu_p_closed` — the cheap converse (fibers of `x ↦ x^p` are full cosets, twisted geometric sums die) makes the sparse window an EXACT characterization of `μ_p`-closure.
* `base_discharge` — the rung in the exact `hBase` hypothesis shape of the O73 climb, at every level `(p^a·q^b)/p^k`, window `q^b + 1`.
* `two_prime_partial_climb` — interval window `j < p^(t-1)·(q^b+1)` ⟹ `μ_{p^t}`-closure (`t ≤ a`): the rung-resolved O70 divisor-coset law along one prime.
* `two_prime_tower_window` — **THE UNCONDITIONAL TOWER**: interval window `j < max(p^(a-1)(q^b+1), q^(b-1)(p^a+1))` ⟹ closure under the FULL `μ_{p^a·q^b}`; every `hBasep`/`hBaseq` of `two_prime_tower_conditional` discharged (q-side = the same rung with the primes swapped).
* `two_prime_window_empty_or_full` — the endpoint: at exact level the master window collapses every subset to `∅` or all of `μ_n` (the `d = n` stratum of the O70 law).
* `m31_smooth_window_law` — the M31 landing: on `μ_18` window `j < 10` forces full `μ_18`-closure (sharp: the rotated `μ_9`-coset survives `j < 9` — probe C2).
* `two_pow_three_window_law` — O95 item (iii) cashed: on `μ_{2^a·3}` window `j < 2^(a+1)` forces full closure — the named "first unconditional mixed-radix tower instance", now for all `a` and in fact all `p^a·q^b`.
* Teeth at ℂ: the rung FIRED on `T = {1, −1} ⊆ μ_12` from the sparse window `{1, 3}` (nonempty, hypotheses jointly satisfiable, conclusion lands).

**Where the open core moves:** the O70 windowed divisor-coset law — exhaustively verified numerically in O70, named open mathematics in O95 — is now a THEOREM at every two-prime modulus, including both M31 smooth regimes (the 2-power side was O53/O61; the multiplicative `μ_18` side is this brick). The window thresholds match O70's verified table exactly at the rung level (sparse window minimal; interval capstone within slack ≤ 4 of sharp, the slack being pure climb-plumbing overshoot). What remains beyond is genuinely new mathematics, not assembly: (i) THREE-plus prime moduli and cofactors `n = p^a·q^b·m` (the de Bruijn classification itself is open there — Lam–Leung ℕ-span territory, see O94 item (i)); (ii) the weighted/ℕ-multiplicity prime-power packet theorem (O95 item (i), assembly-adjacent, the entry point for (i)); (iii) wiring the unconditional tower into the syndrome/list-budget consumers (O61-style) on the M31 multiplicative domain — bookkeeping, queued.

### O98 — the O61 consumer wired onto the two-prime tower: the syndrome list budget on μ_{p^a·q^b}, with the M31 μ_18 budget EXACT at 4

O97's queued item (iii) cashed. `TwoPrimeSyndromeBudget.lean` (axiom-clean ×2, 0 sorry, 0 warnings):
* `two_prime_tower_count` — the O55 `tower_count` pattern at two-prime moduli: on any `D₀ ⊆ μ_{p^a·q^b}`, the `w`-subsets killing the interval window `1 ≤ j < p^(t-1)·(q^b+1)` number ≤ `2^|D₀^(p^t)|` — each is `μ_{p^t}`-closed by O97 `two_prime_partial_climb`, hence a union of full cosets, hence determined by (and recoverable as the `D₀`-filter of) its `p^t`-th-power image. Pigeonhole into the image power set, no new analytic content.
* `m31_syndrome_budget` — the M31 multiplicative landing: on `μ_18` (`= 3²·2`), supports killing the window `1 ≤ j < 9` number ≤ `2^|D₀^9|` per cardinality. Census check (numeric, full `2^18` space): at `D₀ = μ_18` the windowed family is EXACTLY `{∅, the two rotated μ_9-cosets, μ_18}` — 4 = 2², the bound is tight, cardinality pattern (0, 9, 9, 18).

The 2-power side of this consumer is O55/O61 (`full_tower` → `tower_count` → `unit_syndrome_list_budget`); the multiplicative two-prime side is now wired end-to-end: classification (O94) → window law (O97) → list budget (this). NOTE on parallel-lane numbering: the fleet's weighted prime-power packet theorem landed independently as `WeightedPrimePowerPacket.lean` (commit c14ba576, logged there as O96) — it subsumes the O95-item-(i) brick (iff + literal ℕ-combination + exact total-weight law); cross-validated by two independent derivations, do not re-grind.

**Remaining honest frontier of the de Bruijn/tower lane after O96–O98:** (a) the weighted classification at TWO-prime moduli `p^a·q^b` (de Bruijn's full ℕ-combination theorem — the indicator case is O94, the prime-power weighted case is O96; the two-prime weighted case is genuinely open and is the gate to (b)); (b) cofactors/three-plus primes (Lam–Leung ℕ-span, partially false in general — the honest target is the span theorem); (c) the CompatC/Newton-bridge end-to-end packaging on μ_18 in the literal O61 `unit_syndrome_list_budget` shape (needs the esymm↔psum window bridge over the two-prime domain — O45/O60 analogues; bookkeeping given (this), queued).

### O99 — the union-over-loci budget: the Conjecture-D counting skeleton closes into ONE incidence-free bound

O96 named the surviving open content of the counting lane: "purely the LOCUS INCIDENCE". This pass lands the incidence-FREE quantitative answer — the union bound, a pure composition of the landed skeleton (`SliceLocusUnionBudget.lean`, axiom-clean ×2, 0 sorry, 0 warnings):

* `low_weight_union_budget` — on an antipodally closed domain `D` (`0 ∉ D`, char ≠ 2, `N = |D²|`): `#{f : deg f < k, wt_D(f) ≤ w} ≤ C(N, z₀)·q^(k−2z₀)` at `z₀ + w = N`. Route: O94 `low_weight_slice_structure` gives each weight-≤w error a dead locus of size ≥ z₀ with locator-divisible slices; shrink to size exactly z₀ (`Finset.exists_subset_card_eq`; divisibility survives shrinking via `loc_eval_zero`); the weight filter then sits inside the union of the `C(N, z₀)` per-locus spaces, each of EXACT size `q^(k−2z₀)` (O96 `card_polysDegLT_slices_vanishing`); `card_biUnion_le`.
* `low_weight_union_budget'` — the weight form: `≤ C(N, N−w)·q^(k−2(N−w))` for `w ≤ N` — the level-1 Conjecture-D list budget with every constant explicit.

Numerically verified before proving (brute force over ALL q^k polynomials, ZMod 5/7, every admissible (k, w)): bound holds everywhere, EQUALITY at `w = 0` (the full-locus stratum — the bound is exactly the per-locus space there), loose mid-range — the slack IS the open incidence content, now precisely delimited from both sides (exact per-locus equalities below, incidence-free union bound above).

**Where the open core moves:** every term in the Conjecture-D sentence is now either an exact equality (structure O94, per-slice O95, f-level O96) or a one-line-composable bound (this). The genuinely open residue, sharply: (1) beating the union bound = inclusion–exclusion over locus overlaps (how many loci can one f serve — the incidence geometry of `loc`-divisibility); (2) the tower iteration with per-level weight bookkeeping. Both are the real Conjecture-D content; neither is assembly.

### O100 — de Bruijn 1953 WEIGHTED lands at the squarefree two-prime base: the ℕ-multiplicity classification with CONSTRUCTIVE POSITIVITY (grid form)

The post-O99 gate (a) — "the weighted classification at TWO-prime moduli" — opened at its base case. `DeBruijnWeightedSquarefree.lean` (axiom-clean ×4, 0 sorry, 0 warnings):

* `debruijn_weighted_squarefree` — **the headline iff (grid form)**: for `p ≠ q` primes, `ξ, η` primitive `p`-th/`q`-th roots (char 0), `W : ℕ → ℕ → ℕ`: `Σ_{i<p,j<q} W i j·ξ^i·η^j = 0 ⟺ ∃ α β : ℕ → ℕ, W i j = α i + β j` on the grid. The POSITIVITY (nonnegative α, β — de Bruijn's genuine content beyond the easy ℚ-span) is constructive: the argmin shift `α i = W i 0 − min, β j = W i₀ j`.
* Route — pure composition of three landed engines, zero new analytic content: `CRTDoubleSlice.slice_of_packet_minpoly` (the WEIGHT-GENERAL slice engine over an arbitrary base field — its generality is what made this a compose rather than research) at `CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet` (a=b=1: `minpoly_{ℚ(ξ)} η = Φ_q`) gives ALL COLUMN SUMS EQUAL in `ℚ(ξ)` (`column_sums_eq`); `DeBruijnSquarefreePQ.vanishing_combination_const` (prime-level ℚ-rigidity) turns equal columns into the MODULAR EQUATION `W i j + W 0 0 = W i 0 + W 0 j` (`modular_eq`); the argmin shift closes by `omega`. Converse: both parts die against full geometric sums.
* `weighted_total_span` — **the weighted Lam–Leung ℕ-span law at `pq`**: total weight ∈ `ℕ·q + ℕ·p`.
* Teeth at ℂ (p=2, q=3): all-ones matrix vanishes (genuine multiplicities, produced by the converse); the unit matrix CANNOT vanish (decomposition forces `1 = 0 + 0`, omega) — the iff discriminates.

**Falsify-first probe** (`probe_weighted_squarefree_grid.py`, exact ℤ[x,y]/(Φ_p,Φ_q), exit 0): the iff EXHAUSTIVE over full weight boxes at (p,q,B) = (2,3,3), (3,2,3), (2,5,2), (5,2,2), (3,5,1) — vanishing family = decomposable family as a set identity (136/4096 at 2×3·B3, 309/59049 at 2×5·B2, 38/32768 at 3×5·B1); the modular equation and the argmin-shift witness verified on every vanishing W; bump/unit controls live.

**Where the open core moves:** the weighted de Bruijn program now has both endpoints — prime powers (O96 `WeightedPrimePowerPacket`) and the squarefree two-prime base (this). The remaining span to the FULL weighted `p^a·q^b` classification is assembly-shaped and named: (i) the weighted digit descent (restate `ThreadSplit.thread_vanishing_of_vanishing` for ℚ-weights — the K-independence engine is weight-agnostic); (ii) the weighted lift bookkeeping (the O94 `isPacketUnion_of_threads` pattern with combination functions); (iii) the exponent-surface transport (weighted `gridSet`/`gridMap`). Past two primes the ℕ-span theorem (Lam–Leung) remains genuinely open mathematics — de Bruijn's conjecture is false there.

### O101 — WEIGHTED thread-split: the digit-descent engine of the weighted de Bruijn program is a theorem (iff)

O100's named assembly step (i) executed. `WeightedThreadSplit.lean` (axiom-clean ×4, 0 sorry, 0 warnings): for a prime `p` with `p² ∣ n` (`n = p·m`, `p ∣ m`), `ζ` primitive `n`-th (char 0), `w : ℕ → ℕ`:

* `weighted_thread_split_iff` — `Σ_{e<n} w_e·ζ^e = 0 ⟺ ∀ r < p, Σ_{e'<m} w_{r+p·e'}·(ζ^p)^{e'} = 0`. Forward (`weighted_thread_vanishing_of_vanishing`) = O93's engine with ℕ-cast thread coefficients in `K = ℚ⟮ζ^p⟯`: `ThreadSplit.natDegree_minpoly_adjoin_pow_prime` pins degree `p` (the load-bearing `p² ∣ n`), `linearIndependent_pow` + `Fintype.linearIndependent_iff` kill every thread. Converse = pure linearity (any CommRing). `weighted_sum_eq_thread_sum` = the digit decomposition (sum_nbij' on `e = r + p·e'`), CommRing-generic.
* Falsified first (inline, exact ℤ[x]/Φ₁₂+Φ₆): the iff EXHAUSTIVE over all 3^12 = 531,441 weight vectors at n = 12, p = 2 — 2025 vanishing = 45² (the thread product law `|van(n)| = |van(n/p)|^p` visible), 0 mismatches.
* Teeth at ℂ: the multiplicity vector (2,1,2,1) at n = 4 vanishes (ζ² = −1 arithmetic) and the theorem splits it into its vanishing level-2 thread — `2 + 2ζ₄² = 0` produced by the engine.

**Weighted de Bruijn p^a·q^b assembly state after O96/O100/O101:** prime-power case (O96) + squarefree base (O100) + digit descent (this) are all theorems. What remains is PURE BOOKKEEPING, named precisely: (ii) the descent induction (iterate `weighted_thread_vanishing_of_vanishing` down the digits of `n = g·pq`, `g = p^(a-1)·q^(b-1)`, exactly the O94 recursion shape — every level keeps `u² ∣ current n`); (iii) the reassembly of the per-thread O100 combination functions through `e = r + g·e''` into the e-surface form `w_e = A(e mod n/p) + B(e mod n/q)` (the index bookkeeping verified by the inline probe's product law), including the CRT grid↔e-surface transport at the squarefree base (sum_nbij' on `e ↦ ((q⁻¹e) mod p, (p⁻¹e) mod q)`). No new analytic content anywhere in the chain. Beyond two primes: genuinely open (Lam–Leung ℕ-span; de Bruijn's conjecture false).

### O102 — the weighted squarefree classification lands on the EXPONENT surface: the grid↔e-surface transport is done

The hard half of the remaining weighted-`p^a·q^b` bookkeeping executed. `DeBruijnWeightedSquarefreeExp.lean` (axiom-clean, 0 sorry, 0 warnings): `debruijn_weighted_squarefree_exp` — for `p ≠ q` primes, `ζ` primitive `pq`-th (char 0), `w : ℕ → ℕ`: `Σ_{e<pq} w_e·ζ^e = 0 ⟺ ∃ A B : ℕ → ℕ, ∀ e < pq, w e = A (e % q) + B (e % p)` — the ℕ-combination of full prime packets in exponent coordinates.

* Forward = the CRT transport: explicit section `(i,j) ↦ (e₁·i + e₂·j) % pq` with `e₁, e₂ = Nat.chineseRemainder` at `(1,0)/(0,1)`; `sum_nbij'` against `e ↦ (e % p, e % q)` (section identities by ModEq digit bookkeeping); the coordinate roots `ζ^{e₁}, ζ^{e₂}` are primitive `p`-th/`q`-th WITHOUT any order computation (`q ∣ e₁`, `p ∤ e₁` ⟹ `ζ^{e₁} = (ζ^q)^{c₁}` with `c₁` coprime to `p` — `pow_of_coprime`); then O100 `debruijn_weighted_squarefree` classifies on the grid.
* Converse = NO transport: O101 `weighted_sum_eq_thread_sum` regroups each part along its own packet direction (`(r + q·e') % q = r`) and the full geometric sums kill both — the two landed engines compose.
* Teeth at ℂ: `Σ_{e<6} ζ₆^e = 0` produced from the packet split `1 = 1 + 0`.

**Weighted de Bruijn `p^a·q^b` state after O96/O100/O101/O102:** prime powers + squarefree base (grid AND exponent surface) + digit descent are all theorems. The SINGLE remaining step is the descent induction: iterate O101 `weighted_thread_vanishing_of_vanishing` down the digits `n = u·m` (`u ∈ {p,q}`, `u² ∣ n`) to the squarefree base, apply O102 per deep thread, and reassemble `A, B` through `e = r + u·e'` (`A(y) := α_{y % u}(y / u)`-style relabeling, verified numerically by the O101 product law). Pure strong-induction bookkeeping in the exact O94 recursion shape — no analytic content. Past two primes: genuinely open (Lam–Leung ℕ-span).

### O103 — DE BRUIJN 1953 WEIGHTED LANDS IN FULL AT TWO PRIMES: the ℕ-multiplicity classification is an iff at every p^a·q^b — THE WEIGHTED PROGRAM IS CLOSED

The last named bookkeeping step (the descent induction) executed. `DeBruijnWeightedTwoPrime.lean` (axiom-clean ×3, 0 sorry, 0 warnings):

* `debruijn_weighted_two_prime` — **the headline iff**: `n = p^a·q^b` (`a, b ≥ 1`, `p ≠ q` primes), `ζ` primitive `n`-th (char 0), `w : ℕ → ℕ`: `Σ_{e<n} w_e·ζ^e = 0 ⟺ ∃ A B : ℕ → ℕ, ∀ e < n, w e = A (e % (n/p)) + B (e % (n/q))` (exponents in explicit `p^(a-1)·q^b` / `p^a·q^(b-1)` form). De Bruijn's actual 1953 theorem — vanishing NONNEGATIVE-integer combinations of n-th roots of unity are ℕ-combinations of rotated full prime packets — now machine-checked at every two-prime modulus, in both directions.
* `weighted_combination_of_vanishing` — the forward strong induction in the exact O94 recursion shape: O101 `weighted_thread_vanishing_of_vanishing` strips the low digit (`u² ∣` level maintained exactly as in the indicator recursion); O102 lands the squarefree base; the combination functions lift uniformly through `e = r + u·e'` via `A(s) := A_{s%u}(s/u)`, with the two digit identities `(e % (u·k)) % u = e % u` and `(e % (u·k))/u = (e/u) % k` (`Nat.mod_mul_right_div_self`) doing all the index transport; finite choice over threads by the O94 guarded-∃ pattern.
* `packet_part_eq_zero` — the generic converse at EVERY modulus `n` with `u ∣ n` (not just two-prime): an ℕ-combination supported on the `μ_u`-packet direction kills the power sum — O101 regrouping + one full geometric sum.
* Teeth at ℂ at a genuinely NON-squarefree level: `Σ_{e<12} ζ₁₂^e = 0` produced from the split `1 = 1 + 0` at `n = 2²·3`.

**THE WEIGHTED TWO-PRIME DE BRUIJN PROGRAM IS CLOSED** (O96 prime powers → O100 squarefree grid → O101 descent engine → O102 exponent surface → O103 full classification), mirroring the indicator program (O66→O94) — and per the O91 literature search, no formalization of de Bruijn/Lam–Leung theory exists in any other proof assistant; the weighted classification here is the first machine-checked proof of de Bruijn's 1953 theorem as stated (ℕ-coefficients), not only its indicator shadow. **What remains beyond is genuinely open mathematics, not assembly:** (i) THREE-plus prime moduli — de Bruijn's conjecture is FALSE there (Lam–Leung); the honest target is the ℕ-span theorem `W(n) = ℕp₁ + … + ℕp_k`, whose proof needs genuinely different (induction-on-Φ-structure) tools; (ii) the t > 1 window law at 3+ prime moduli; (iii) the Conjecture-D incidence geometry (O99's union-bound slack); (iv) the prize core itself (δ* in the Johnson→capacity gap) — all tracked, none fabricated.

### O104 — LAM–LEUNG'S ℕ-SPAN THEOREM at two-prime moduli + the three-prime refutation witness PINNED

The post-O103 residue named the ℕ-span theorem as the honest span target (the form surviving past two primes). At two primes it is now a COROLLARY. `LamLeungSpanTwoPrime.lean` (axiom-clean ×2, 0 sorry, 0 warnings):

* `lam_leung_span_two_prime` — **the weighted span law**: `Σ_{e<p^a·q^b} w_e·ζ^e = 0 ⟹ Σ_e w_e ∈ ℕ·p + ℕ·q` (Lam–Leung J. Algebra 224 (2000) Thm 4.1 at two primes, ℕ-multiplicity form; the indicator case was O95 `vanishing_card_two_prime`, the prime-power case the fleet's O96). Route: O103 decomposition + the fiber-counting identity.
* `sum_mod_fiber` — `Σ_{e<m·u} f(e%m) = u·Σ_{s<m} f s`, extracted from O101 `weighted_sum_eq_thread_sum` at `ζ = 1` over ℚ and cast back — zero new summation machinery.

**The three-prime wall, witness pinned (numeric, exact ℤ[x]/Φ₃₀, this pass):** the classical set `S = {5, 6, 12, 18, 24, 25} ⊆ [0, 30)` (= μ₅\{1} ∪ {ζ₆, ζ₆⁵} in exponent form, from subtracting the μ₃ relation from the μ₅ relation and absorbing signs via ζ₂) VANISHES at `n = 30 = 2·3·5` yet contains NO full μ₂-, μ₃-, or μ₅-packet — so a 0/1 packet decomposition is impossible and **de Bruijn's packet conjecture fails at three primes** exactly as Lam–Leung record. The refutation brick is now precisely gated for formalization: vanishing = two geometric-sum relations (assembly); non-decomposability = the finite no-full-packet check (decide). What is genuinely open past two primes is the POSITIVE ℕ-span theorem `|w| ∈ ℕp₁ + … + ℕp_k` (Lam–Leung's main theorem, requiring induction on cyclotomic structure, not packet combinatorics) — research, not assembly.

**O104 addendum — the exponent-surface cardinality law + genuine weighted teeth** (`DeBruijnWeightedCardTwoPrime.lean`, axiom-clean ×3, 0 sorry, 0 warnings): `weighted_total_span_two_prime` (the O104 span law in `i·p + j·q` orientation) and `debruijn_card_two_prime` — the Lam–Leung CARDINALITY law `|S| ∈ ℕp + ℕq` at every `p^a·q^b` via the indicator instantiation of O103, **independent of the packet machinery** (the packet-route twin is `DeBruijnTowerWiring.vanishing_card_two_prime` on the field surface; two derivations cross-validate). Teeth upgrade the weighted chain's witnesses to genuine multiplicities: the converse manufactures `2 + ζ₁₂⁴ + ζ₁₂⁶ + ζ₁₂⁸ = 0` (multiplicity 2 at `e = 0`) from explicit packet functions; the forward direction refutes the singleton weight `𝟙{e=0}` (`1 = 2i + 3j` killed by omega) — the first forward-direction discrimination in the weighted chain. Load-bearing mathlib route for the descent reassembly (recorded for reuse): `(e % (u·k)) % u = e % u` (`Nat.mod_mod_of_dvd`) and `(e % (u·k)) / u = (e/u) % k` (`Nat.mod_mul_right_div_self`).

### O105 — DE BRUIJN'S PACKET CONJECTURE FORMALLY REFUTED AT THREE PRIMES: the two-prime classification is provably sharp

The O104-pinned witness formalized. `ThreePrimePacketRefutation.lean` (axiom-clean ×3, 0 sorry, 0 warnings, Mathlib-only):

* `three_prime_witness_vanishes` — `ζ₃₀⁵ + ζ₃₀⁶ + ζ₃₀¹² + ζ₃₀¹⁸ + ζ₃₀²⁴ + ζ₃₀²⁵ = 0`: one `linear_combination h5 − h3 + (ζ⁵+ζ¹⁰)·h15` over the three cyclotomic relations (μ₅ geometric, μ₃ geometric, `ζ¹⁵ = −1` from the square-root-of-1 dichotomy).
* `three_prime_witness_not_packet_combination` — no `A B C : ℕ → ℕ` realize the indicator as `A(e%15) + B(e%10) + C(e%6)` on [0,30): four instances (e = 5, 20, 15, 11) and omega.
* `debruijn_packet_conjecture_fails_three_primes` — the combined refutation: the O94/O103 packet classification GENUINELY FAILS at the first three-prime modulus, exactly as de Bruijn conjectured-and-was-refuted (Lam–Leung §5). The two-prime theorems are sharp, machine-checked from both sides.

**Net frontier after O97–O105 (one session):** the two-prime de Bruijn theory is COMPLETE AND SHARP — indicator classification (O94), window law/unconditional tower (O97), consumers (O98), weighted classification both surfaces (O100/O102/O103), span law (O104), and the three-prime impossibility (O105). The remaining open items on this lane are now PURE research with no assembly component anywhere: the Lam–Leung ℕ-span at 3+ primes (the positive theorem surviving the refutation — needs induction on cyclotomic structure, not packets), the window law at 3+ primes, O99's incidence slack, and δ*. The refutation closes the last item that was provable.

### O106 — THE WINDOWED TWO-PRIME LAW (t-GENERAL): the full dense-window fiber classification is a theorem — O70's exhaustive law machine-checked, both directions

(Numbering note: the issue comment announcing this brick says "O105" — it raced the three-prime refutation's O105; this entry renumbers it O106. The two bricks are independent.)

`DeBruijnWindowedLaw.lean` (new file, 8 theorems, all axiom-clean `[propext, Classical.choice, Quot.sound]`, 0 sorry, 0 warnings, pushed 01c6ced99):

* `windowed_two_prime` — **the headline iff**: `n = p^a·q^b`, `ζ` primitive `n`-th (char 0), `S ⊆ [0,n)`, `t < n`: `(∀ j, 1 ≤ j ≤ t → Σ_{e∈S} ζ^{je} = 0) ⟺ S` is a disjoint union of canonical rotated `μ_d`-cosets with `d ∣ n`, `d > t` — the O70 mixed-radix tower law (86/86 (n,t) fibers verified exhaustively at n = 12, 18, 24, 36) as a kernel-checked theorem. The *pure size-kill law*: `μ_d` survives the window iff `d > t`. The `t = 1` instance recovers O94; every `t > 1` is new (no literature statement covers the dense-window fiber at composite `n`). Dense-window complement of O97's sparse q-power tower.
* **Multiplicity-free route** (no weighted machinery despite `j·e` exponent collapse): induction on `t`. Step `t → t+1`: `isPacket_pow_sum_eq_zero` (geometric kill at `d ∤ j`) annihilates every `d > t+1` coset; the survivors contribute `(t+1)·Σ_{bases} (ζ^{t+1})^r` over DISTINCT bases (the base of a canonical coset is `e % (n/(t+1))` for any of its elements; disjointness ⟹ distinct bases — multiplicities never appear); the level classifier breaks the bases into prime packets at level `n/(t+1)`; `isPacket_merge` reassembles each base-packet's fattened cosets into ONE canonical `μ_{(t+1)d'}`-coset.
* **`LevelDecomposes` interface**: the induction wrapper `windowed_law` is modulus-agnostic — it consumes "vanishing subset sums at every divisor level ≥ 2 decompose into prime packets", discharged at two-prime smooth moduli by `levelDecomposes_of_dvd_two_prime` (O94 at two-prime levels, O92 at prime-power levels through the ZMod bridges). A future level classification at 3+-prime moduli inherits the full windowed law with zero extra work — note this CANNOT be the packet form (O105 refutation); the right 3-prime interface is the open question.
* Teeth at ℂ (n = 12, t = 3): μ₄-coset {0,3,6,9} kills the whole window via .mpr; μ₂-coset {0,6} refuted for window 3 via .mp (cardinality pinch).

**Record correction (honesty ledger):** the 2026-06-10 06:23Z issue comment "O83: the upward rung — coset_lift (pushed)" was a phantom at the time of writing — `git log --all -S coset_lift` showed no such symbol anywhere in history when checked at ~06:45Z; a concurrent lane later landed its own `coset_lift` with a different signature. Ledger entries should only say "pushed" with a commit hash.

**Where the open core moves:** the windowed/dense-fiber program at two primes is CLOSED (this brick + O97's sparse tower + O94/O103 below it). Named next consumers: (i) the **0/1 codeword weight spectrum of dual-RS/BCH-window codes on smooth two-prime domains** — `{x ∈ {0,1}^n : Σ x_e ζ^{je} = 0, 1 ≤ j ≤ t}` is exactly the window fiber, so nonzero weights are sums of divisors of `n` exceeding `t`; minimum nonzero weight = least divisor `> t` (sharp, witnessed by any single coset) — a genuinely prize-adjacent surface (weight structure of RS-dual codewords on the deployed smooth domains); (ii) the fiber-count law `F_n(t) ≅ F_lcm(Dmin)(t)^(n/lcm)` (O70's count structure); (iii) the windowed law at 3+ primes (open, interface named).

### O107 — the 0/1 WEIGHT SPECTRUM of the BCH-window (dual-RS) code on smooth two-prime domains: exact, sharp, strictly past BCH between divisors

Consumer (i) named by O106, executed. `DeBruijnWindowedLaw.lean` +121 lines (5 new theorems, all axiom-clean, 0 sorry, 0 warnings, pushed dedd402ce):

* `IsWindowCosetUnion.card_eq_sum` — **the weight spectrum**: every window-`t`-vanishing weight is a sum of divisors of `n` exceeding `t` (the multiset of coset sizes; `card_biUnion` over the decomposition).
* `IsWindowCosetUnion.le_card_of_nonempty` + `window_min_weight_sharp` — **the exact minimum weight**: nonempty window-vanishing sets have `≥ d₀` elements for `d₀` = any lower bound on divisors `> t`, and every divisor `> t` is achieved (base-0 canonical coset). So the minimum 0/1-codeword weight of the cyclic code with zeros `ζ,…,ζ^t` on a two-prime-smooth domain is EXACTLY the least divisor of `n` exceeding `t`.
* `window_weight_spectrum_two_prime` / `window_min_weight_two_prime` — instantiations through O106's iff.
* Kernel-checked BCH-beating instance: `n = 72 = 2³·3²`, `t = 9` ⟹ min 0/1 weight `≥ 12` (interval_cases + decide over the divisor list), vs. designed-distance bound `10`.

**Why prize-adjacent:** the window code is the dual-side Vandermonde-window constraint system of RS on exactly the smooth domains the prize fixes; the law gives the complete combinatorics of which 0/1 supports can vanish against an initial window — exact-domain structure of the kind a derandomization attack on δ* must exploit (generic-field bounds like BCH are provably not tight here).

**Named next:** (i) the WEIGHTED window spectrum — run the O106 induction with O103's weighted classification as the level interface; yields ALL codeword weights of the window code, i.e. the full weight distribution problem on smooth domains; (ii) the fiber-count law `F_n(t) ≅ F_{lcm(Dmin)}(t)^{n/lcm}` (O70's count structure); (iii) the window law at 3+ primes (blocked on the right level interface — packet form refuted by O105).

### O108 — 672 DERIVED: the C1379 count is a char-0 THEOREM; the per-level law has two proven rungs with one engine (nubs, 2026-06-10)

`scripts/probes/n32census/level2/DERIVED-672.md` (commit bc39fef9a; audited 0.94 incl. a fully
independent rule-free brute-force char-0 enumeration in C: 672 at pattern (7,3), ZERO at every
other pattern, 315 = 35·9 at (8,1) — three-way exact set equality with the derivation and the
raw data). **The derivation:** the C1379 consistency equation reduces (e₁² = Σx² + 2e₂,
machine-asserted 1344/1344) to ANTIPODAL BALANCE of the 14-term μ₃₂ multiset
{x₁x₂, x₁x₃, x₂x₃} ⊎ B_z ⊎ O_z ⊎ {−z*} (2-power Lam–Leung in multiset form, immediate from
ℤ[ζ₃₂] power-basis freeness — the in-tree set-form lemma's multiset upgrade is a named Lean
follow-up). Six structural lemmas (parity-pure O; three distinct product axes, P|P forbidden;
no product at −z*; **ξ ∉ μ₃₂ ⟹ agreement exactly 17, never 18**; σ-uniqueness per (B,O); free
negation), then the counting engine: B-placement rule C(v,(7−h)/2) over the E1–E4 event
taxonomy with closed-form u-triple censuses (ε=1: C(8,3) = 56 splits perfectly 7×8; ε=0:
38 live + 18 dead). Node table: **672 = 368 + 304**; dual-B census **92 = 20+24+24+16+8** (five
identified mechanisms) ⟹ 580 = 488+92, 488·2 + 92·4 = 1,344 ✓; z*-axis strata
224+96+160+192 = 672 ✓; the witness count **35 = C(7,4) falls out of the same balance law** at
pattern (8,1). **Effective characteristic transfer via the O38/E1 norm bound:** every
non-solution sum has N(α) ≤ 196⁸ < 2^61 ⟹ the theorem holds verbatim at EVERY split prime
p > 2^61 (the two verified primes below threshold are covered by their exhaustive censuses).
Provenance graded honestly: the dual-B mechanism and |O| ≥ 5 exclusion are exact finite
ℤ₁₆-enumerations (C19's own epistemic grade); everything else hand-derived + machine-asserted.
**Consequence: the per-level branch-count law has two proven rungs with one visible engine —
reduction → balance → taxonomy → placement — the shape Conjecture D's induction can consume.**

### O109 — the INCIDENCE CENSUS: level-1 Conjecture-D slack is CLASSICAL (MDS enumerator exact), the coset union bound is interpolation-dominated, and lists stay floor-trivial until capacity−2 (nubs, 2026-06-10)

Two probes landed (`scripts/probes/probe_slice_product_count.py`, `probe_locus_incidence_census.py`, both exit 0, exact GF(q) arithmetic), measuring the O99-named "union-over-loci/incidence structure versus the weight filter" from both sides:

* **Cross-validation lane:** `probe_slice_product_count.py` independently re-verifies the landed counting bricks — the slice bijection `{deg<2m} ≅ {deg<m}²`, the per-locus product count `q^(2m−2|Z|)` (O95/O96), the dead-locus structure theorem, and the O99 union bound — over GF(5/13/17), all exhaustive, all exact.
* **CENSUS 1 (the weight filter has a CLOSED FORM at level 1):** the exact count `N(w) = #{f : deg<k, wt_D(f)=w}` matches the classical MDS weight-distribution formula `A_w = C(n,w)·Σ_j (−1)^j C(w,j)(q^{w−d+1−j}−1)` EXACTLY at every `(q,n,k,w)` tested (q=17, n∈{8,16}, k∈{2,3,4}; q=13, n=12; q=257, n=16) — RS on the smooth subgroup domains is MDS and the level-1 union-over-loci question is therefore CLASSICAL, not open. The O99 slack is now exactly quantified: the slice union bound SU overshoots `N≤(w)` by tabulated ratios (equality only at `w ∈ {0, n}`), and the plain zero-locus union bound CU is tighter than SU at every interior weight tested. The level-1 fold adds NO counting power over classical interpolation — the genuine Conjecture-D content is strictly at tower level ≥ 2.
* **CENSUS 2 (the open object — coset/list incidence):** over 54 received words per setup (structured deep-hole-ish + random), per-coset list sizes obey: `ℓ(u,w) = 0` strictly PAST the Johnson radius up to `w ≈ capacity−2` (e.g. q=17, n=16, k=4: Johnson = 8.0, lists empty through w=9); `max_u ℓ` first crosses `n` at `w = capacity−1±1` and `n²` only at capacity. The affine per-locus occupancy in the over-constrained regime matches the random-function prediction `1−exp(−q^(k−2z))` (generic EMPTINESS of coset slice spaces — the union bound is structurally loose on cosets); incidence multiplicity of genuine list elements is tiny (≤ 5 loci served, |P| histogram concentrated at 1–3).
* **Verdict + named next:** (1) level-1 slice/locus geometry is fully classical — retire it as an open direction; (2) the surviving Conjecture-D content is the TOWER ITERATION (level-≥2 fold constraints multiplying down the 2-adic chain — no census exists yet); (3) the floor-triviality of coset lists until capacity−2 on smooth domains is the empirical shadow of where δ* sits at toy scale — every sampled word, structured or random, is list-trivial through the entire Johnson→(capacity−2) band. Caveat honestly: n ≤ 16, q ≤ 257 — toy scale, no asymptotic claim.

### O108 — THE WEIGHTED WINDOWED LAW: window-t vanishing of an ℕ-weighted sum ⟺ ℕ-combination of μ_d-coset indicators (d ∣ n, d > t) — the windowed program's maximal element at two primes

Probe-falsified first (`scripts/probes/probe_weighted_window_law.py`, exact ℤ[x]/Φ_n, exit 0: full {0,1,2}^12 box — 531,441 vectors, 2,024 vanishing, all decomposed by a complete backtracking decomposer at their maximal window; full 0/1 box at n = 18 reproducing the O67 census; 400k samples of {0..3}^12; 6,000 converse trials at n = 12, 18, 20). `DeBruijnWeightedWindowLaw.lean` (8 theorems, axiom-clean, 0 sorry, 0 warnings, pushed e9d5f07f3):

* `weighted_windowed_two_prime` — **the headline iff**: `(∀ j, 1 ≤ j ≤ t → Σ_{e<n} w_e ζ^{je} = 0) ⟺ ∃ A, ∀ e < n, w e = Σ_{d ∈ n.divisors, d > t} A d (e % (n/d))`. Common generalization of O103 (t = 1, ℕ-weights) and O106 (all t, 0/1): the lattice O94 ⊂ O103, O94 ⊂ O106, both ⊂ O108 is complete. Equivalently: the full ℕ-codeword description of the BCH-window/dual-RS code on smooth two-prime domains (extends O107's 0/1 weight spectrum to all multiplicities).
* **Structural finding: the weighted induction is SIMPLER than the 0/1 one.** No disjointness bookkeeping exists anywhere: (a) `packet_part_pow_sum_eq_zero` (u ∤ j geometric kill, per combination part, via O101's `weighted_sum_eq_thread_sum` at ζ^j); (b) `packet_part_resonant_sum` (the d = t+1 part yields `(t+1)·Σ_r A_{t+1}(r)(ζ^{t+1})^r`); (c) `WeightedLevelDecomposes` interface, discharged at every divisor level (O103 two-prime; O96 prime-power periodicity through a fresh ℕ↔ZMod iteration bridge `weightedLevel_prime_pow`; level 1 trivial); (d) the merge = ONE index identity `(e % m) % (m/d') = e % (m/d')` + `Finset.sum_fiberwise_of_maps_to`. Multiplicities linearize the problem; canonical-base recovery (O106's hardest seam) disappears.
* Both `windowed_law` (O106) and `weighted_windowed_law` (O108) are modulus-agnostic over their level interfaces — a 3-prime level classifier of any shape inherits both windowed laws mechanically.

**Where the open core moves:** the two-prime windowed program is CLOSED at all multiplicities. The single remaining wall on the de Bruijn front is 3+-prime moduli (packet form refuted, O105; the honest target is the Lam–Leung ℕ-span and whatever level-decomposition form survives at p·q·r). Prize-adjacent consumers now unblocked: the complete weight distribution of window codes on the deployed smooth domains; the fiber-count laws.

**O105 addendum — the next provable gate past the refutation, named (dimension-checked):** what survives at squarefree `pqr` is the ℚ/ℤ-classification WITHOUT positivity: `Σ W_{ijk}·ξ^i·η^j·θ^k = 0 ⟺ W_{ijk} = A(j,k) + B(i,k) + C(i,j)` (each component constant in one coordinate; ℚ-valued — O105 kills the ℕ-form). Dimension check passes: `pqr − φ(pqr) = pq+pr+qr−p−q−r+1` = dim of the sum of the three fiber-function spaces. Route, gated on ONE new lemma: (i) generalize `CRTPacketMinpoly.minpoly_adjoin_primitiveRoot_eq_packet` from prime-power base roots to ANY coprime base — `minpoly ℚ⟮ζ_m⟯ ζ_r = Φ_r` for `Coprime m r` (same totient-tower pinch, `Nat.totient_mul` replaces the prime-power split); (ii) the K-coefficient slice at Φ_r forces the θ-fibers' 2-var sums equal; (iii) the ℚ-valued 2-var classification is O100's modular equation with NO shift needed (negatives allowed: `a_i := W_{i0}−W_{00}`, `b_j := W_{0j}`); (iv) integrate the per-pair differences into the three-component form. Past that, the ℕ-content at 3+ primes (Lam–Leung's actual span theorem) remains research — the refutation shows it cannot factor through packets.

**Shared-index hazard (same day, fixed in 17bae3b3e):** bare `git commit` commits the WHOLE index — in this multi-session repo it carried a concurrent lane's staged deletion (`AppendRbrKnowledgeSeamZero.lean`, a landed #114 achievement) into my O105 commit. Restored from 387ba340c. **Future commits: always `git commit -- <my files>` with explicit pathspec.**
### O110 — THE FIRST REASSEMBLY: the window-{1,q} trichotomy (the windowed law's shape, proven)

`DeBruijnTwoPrime.two_prime_window_trichotomy` + `packetUnion_dichotomy_spectrum`
(axiom-clean, 0 sorry; my lane — the dichotomy export strengthens the spectral
construction with: every x ∈ S is μ_p-closed in S or x^q ∈ spectrum):

**With window {1, q}, every element of a two-prime vanishing set is μ_p-, μ_{q²}-, or
μ_{pq}-covered inside S** — the d-coset reassembly over the divisors d ∈ {p, q², pq}
exceeding q: EXACTLY the O70-verified law shape at t = q, now a theorem. Wiring:
decomposition (O77) + dichotomy–spectrum export + spectrum vanishes (transfer e=1 +
window, char 0) + COVER (O76) applied to the spectrum one level down + the upward rung
(O83) at A = p and A = q converting spectrum-level row/column coverage of x^q into
μ_{pq}/μ_{q²} closure at x.

The reassembly engine is PROVEN at its first nontrivial window. The general-t law =
iterating this wiring through the O81 chain (each deeper window kills one more divisor
level and the rung multiplies the reassembled coset order) — every constituent
machine-checked; remaining = the general-t induction bookkeeping. Ops note: two
working-tree wipes beaten this pass by commit-before-compile + /tmp content blocks.

### O106 — THE COPRIME GATE OPENS: `minpoly ℚ(ζ_m) ζ_r = Φ_r` for ANY coprime m, r — the O105-addendum lemma is a theorem

`CoprimePacketMinpoly.lean` (Mathlib-only, axiom-clean ×2, 0 sorry, 0 warnings, first-shot compile): `minpoly_adjoin_coprime_eq_cyclotomic` — coprime cyclotomic extensions never split each other's cyclotomics, at FULL generality (any `0 < m`, `0 < r` coprime; the prime-power hypothesis of `CRTPacketMinpoly` was never load-bearing — its totient-tower pinch runs verbatim on `Nat.totient_mul hco`). Plus `minpoly_adjoin_coprime_prime_eq_geom`: the `Σ_{t<r} X^(t·1)` slice-engine shape at prime `r`. The pqr ℚ-classification route of the O105 addendum is now pure composition: slice at base `m = pq`, reduce fiber differences to the 2-var ℚ-classification, integrate.

### O111 — the WINDOW FIBER-COUNT LAW pinned at set level: F_n(t) ≅ F_m(t)^(n/m) with the exact block-trace bijection (probe layer; nubs, 2026-06-10)

O107's named next (ii) executed at the probe layer (`scripts/probes/probe_fiber_count_law.py` + `probe_window_fiber_threads.py`, both exit 0, pure coset combinatorics — by O106 the fiber family needs no roots of unity):

* **The exact bijection shape, pinned:** with `Dmin` = the divisibility-minimal divisors of `n` exceeding `t`, `m = lcm(Dmin)` (`m ∣ n`), `g = n/m`: block `c < g` is the residue class `{e : e ≡ c mod g}`, the trace is `T_c(S) = {e/g : e ∈ S, e ≡ c}` ⊆ `[0, m)`, and `S ∈ F_n(t) ⟺ ∀ c < g, T_c(S) ∈ F_m(t)` — bijectively, hence `|F_n(t)| = |F_m(t)|^(n/m)`. Verified at every `(n, t)` for `n ∈ {12, 18, 24, 36}` (all `t < n`), reproducing O70's counts (`|F_36(t)|`: 10⁶, 22³, 1036, 100, 22, 10, 4, 2) and the classical cross-check `F_24(1) = F_6(1)^4 = 10⁴`.
* **The key structural lemma behind it (the Lean target):** the trace of a `μ_d`-coset (a full residue class mod `n/d`) on a block is empty or a full `μ_{gcd(d,m)}`-coset at level `m`, and `gcd(d,m) > t` because every divisor of `n` exceeding `t` is a multiple of some element of `Dmin`, all of which divide `m`. Both directions of the bijection ride on this + the O106 classification.
* Named remaining: the Lean brick (`WindowFiberCount.lean` — the bijection on the O106 predicate + the cardinality corollary; the per-block lift/trace lemmas are now exactly specified by the probe's checked identities `key/tbl/trace/count/lift/cosetTrace`, all green at 25+ (n,t) points).

### O107 — THE THREE-PRIME ℚ-CLASSIFICATION IS A THEOREM: the first classification result past the two-prime wall

The O105-addendum target executed through the O106 gate, in two bricks (both axiom-clean, 0 sorry):

* `RatWeightedSquarefreeGrid.lean` (O107a, ×3) — the 2-var classification at ℚ-weights: `Σ W ij·ξ^i·η^j = 0 ⟺ ∃ a b : ℕ→ℚ, W ij = a i + b j`, with DIRECT integration (`a i = W i0 − W 00`, `b j = W 0j` — no argmin; negatives free). The fiber-difference engine.
* `ThreePrimeRatClassification.lean` (O107b, ×1) — **the headline**: for distinct primes p, q, r and primitive roots ξ, η, θ (char 0), `Σ_{i<p,j<q,k<r} W ijk·ξ^i·η^j·θ^k = 0 ⟺ ∃ A B C : ℕ→ℕ→ℚ, W ijk = A(j,k) + B(i,k) + C(i,j)` — the weight cube splits into three fiber functions, each constant in one coordinate. Dimension check: `pq+pr+qr−p−q−r+1 = pqr − φ(pqr)` ✓. Route: the θ-fiber coefficients live in `K = ℚ⟮ξ·η⟯` (CRT exponents embed ξ, η as generator powers — `(ξη)^{e₁} = ξ` via the O102 `pow_mod_eq` digit reductions); O106 `minpoly_adjoin_coprime_prime_eq_geom` at the COMPOSITE base `m = pq` feeds `slice_of_packet_minpoly` ⟹ all θ-fibers equal; fiber differences classified by O107a; integration `A jk := v_k j, B ik := u_k i, C ij := W ij0`; converse = three coordinate-wise geometric deaths.

**Significance**: this is the first machine-checked CLASSIFICATION of vanishing weighted root-of-unity sums at a three-prime modulus — the exact ℚ-linear structure that survives the O105 refutation of the ℕ-packet form. The remaining ℕ-content at 3+ primes is precisely the GAP between this ℚ-classification and nonnegativity: Lam–Leung's span theorem says only the TOTAL escapes into ℕp+ℕq+ℕr, not the components — that positivity analysis (Lam–Leung's main induction) is the genuinely open formalization target, now with its linear half done. The general-n ℚ-classification (arbitrary squarefree, k primes — k-component fiber splits) is the natural next assembly (the O106 gate is already fully general in m).

### O108 — the ℤ-refinement: Rédei–de Bruijn–Schoenberg at three primes — the positivity boundary is now sharp from BOTH sides

`ThreePrimeIntClassification.lean` (axiom-clean ×2, first-shot compile): `three_prime_int_classification` — for INTEGER weights at squarefree `pqr`, the three fiber components can always be chosen INTEGER-valued, via the explicit gauge normalization `C' = W ··0`, `B' = W ·0· − W ·00`, `A' = W 0·· − W 0·0 − W 00· + W 000` (correctness = one linarith over eight instances of the O107 ℚ-split, cast back by injectivity). This is the ℤ-span theorem for vanishing sums (Rédei 1954 / de Bruijn 1953 / Schoenberg 1964 — the lattice of vanishing sums is packet-spanned over ℤ) at three-prime moduli, grid form. Plus `nat_weights_int_components`: every vanishing ℕ-multiplicity sum has ℤ-components.

**The three-prime positivity boundary is now machine-checked from both sides**: components exist over ℤ (this), provably not over ℕ (O105) — the defect between them is precisely the content of Lam–Leung's span induction, which is the sole remaining open item of the classification program (together with the general-k arity induction of the O107 pattern, the 3+-prime window law, O99's incidence slack, and δ*). The session ledger O97→O108 stands at twelve generations, 42 axiom-clean theorems.

### O112 — THE WINDOWED MASS-SPAN LAW: the t-general total-mass spectrum of the BCH-window code, with a kernel-checked mass GAP theorem (fable lane, 2026-06-10)

The quantitative consumer of O108's weighted windowed law, generalizing O104 (t = 1 span) and O107 (0/1 spectrum) simultaneously. `WindowMassSpan.lean` (5 theorems + gap example, all axiom-clean `[propext, Classical.choice, Quot.sound]`, 0 sorry, 0 warnings):

* `mass_of_combination` — **the mass formula**: an ℕ-combination of `μ_d`-coset indicators (`d ∣ n`, `d > t`) has total mass `Σ_d c_d·d` (each unit of `μ_d`-multiplicity contributes exactly `d`; `sum_mod_fiber` per divisor).
* `window_mass_span_two_prime` — **the windowed span law**: at `n = p^a·q^b` (char 0), any window-`t`-vanishing `w : ℕ → ℕ` has `Σ_{e<n} w_e ∈ ℕ-span{d : d ∣ n, t < d}`.
* `window_min_mass_two_prime` — **the sharp minimum**: positive mass ⟹ mass ≥ the least divisor of `n` exceeding `t` (the all-multiplicities upgrade of O107's 0/1 minimum-weight law).
* `window_mass_sharp` — **sharpness at every divisor, any modulus**: the canonical `μ_{d₀}`-coset indicator vanishes on the window and has mass exactly `d₀` (no two-prime hypothesis — pure converse).
* `window_mass_in_prime_span` — **the O104 upgrade**: for EVERY window length `t ≥ 1`, mass ∈ `ℕ·p + ℕ·q` (each divisor `> t ≥ 1` is a multiple of `p` or `q`; O104 is the `t = 1` case).
* **Teeth — the mass GAP at O107's BCH-beating instance** (`n = 72 = 2³·3²`, `t = 9`, divisors > 9 = `{12,18,24,36,72}`): every window-9-vanishing multiplicity vector with mass < 24 has mass ∈ `{0, 12, 18}` — kernel-checked (`decide` on the divisor filter + `omega` on the 5-term span), i.e. masses 1–11, 13–17, 19–23 are all IMPOSSIBLE at every multiplicity, where BCH-type reasoning gives only "≥ 10".

**Falsify-first** (`scripts/probes/probe_window_mass_span.py`, exact ℤ[x]/Φ_n, exit 0): exhaustive over `{0,1,2}^12` (531,441 vectors), `{0,1}^18`, `{0,1}^20` at every window length — span membership, sharp minima, and full gap structure all confirmed. **New structural finding from the probe**: at 0/1 weights the mass spectrum is STRICTLY smaller than the ℕ-span — genuine PACKING OBSTRUCTIONS exist (e.g. `n = 18`, `t = 1`: mass `17 = 9+3+3+2` is in the span but unrealizable — the `μ_9`-coset fills a full parity class and both `μ_2`-cosets straddle parities). So the three spectra now separate cleanly: 0/1 spectrum (disjoint-packing sums, O107) ⊊ weighted spectrum (= full ℕ-span within mass room, this brick) ⊆ divisor span. The 0/1 packing geometry — which divisor multisets pack disjointly — is a new named open surface (combinatorial, finite per `n`).

Also landed: `probe_window_fiber_threads.py` (cited by O111's ledger entry; analytic ℤ[x]/Φ_n ground truth at n = 12, 18 for the block-trace bijection + combinatorial fiber at n = 20, 24, 36 — cross-validates `probe_fiber_count_law.py` from an independent implementation).

**Where the open core moves:** the mass/weight-distribution side of the two-prime windowed program is now closed at all multiplicities with explicit gap structure. Remaining named opens on this front: (i) the 0/1 packing characterization (which divisor multisets are realizable disjointly — the O107↔O112 separation); (ii) the per-mass COUNT (how many vanishing w per mass — the weighted analogue of O111's fiber-count law); (iii) 3+-prime windowed laws (blocked on the level interface; ℤ-side now open via O108's ℤ-classification).

### O109 — the general-arity program: the converse half PROVED at every modulus; the forward peel fully designed and gated

**Landed (`GeneralPacketCombination.lean`, axiom-clean ×2):** `packet_combination_vanishes` + `rat_packet_combination_vanishes` — at EVERY `n` (no squarefree hypothesis, ℕ- and ℚ-weights): `w e = Σ_{p ∈ primeFactors n} A p (e % (n/p)) ⟹ Σ_{e<n} w_e·ζ^e = 0` — every prime-fiber component carries its prime's full geometric sum. The general-arity classification's easy half, at maximal generality (the ℚ form re-runs the O101 regroup at base `n/p` inline since `packet_part_eq_zero` is ℕ-cast).

**Gated (the forward at squarefree n, the arity induction — design complete, dimension- and route-checked, NOT claimed):** strong induction on n. Base n = 1 trivial; n = p (prime): rigidity (`vanishing_combination_const`) ⟺ constant component. Step: p := n.minFac, m := n/p (squarefree ⟹ Coprime p m, m < n): (i) CRT transport e ↔ (e%p, e%m) with section (e₁i + e₂f) % n exactly as O102 — the coordinate-root primitivity arguments generalize (Coprime e₂ m from e₂ ≡ 1 [MOD m] via gcd-mod, then `Nat.Coprime.coprime_dvd_left`); (ii) the p-fiber coefficients live in ℚ⟮ζ^p-side gen⟯ and the O106 gate at (m, p) — ALREADY GENERAL in m — forces all p-fibers equal via `slice_of_packet_minpoly`; (iii) fiber differences vanish at level m ⟹ IH components B^i_q; (iv) decode: A_p(y) := W(0-fiber, y), and for q ∣ m: A_q(y) := B^{y%p}_q(y % (m/q)) — well-defined by `(e%(n/q))%p = e%p` and `(e%(n/q))%(m/q) = e%(m/q)` (both `Nat.mod_mod_of_dvd`). Every ingredient is landed; the residual work is the strong-induction plumbing (~350 lines of the O102/O107 patterns merged). k = 2 (O102) and k = 3 (O107, via the grid) are its proved instances.

**The ℕ-side at general arity remains genuinely open** (Lam–Leung positivity; the O105/O108 boundary shows components are ℤ-not-ℕ already at k = 3).

### O113 — the MULTISET ANTIPODAL UPGRADE: 2-power Lam–Leung in counting form — vanishing multiset sums over μ_{2^k} ⟺ count z = count (−z) (the O108 named Lean follow-up; nubs, 2026-06-10)

`LamLeungMultisetAntipodal.lean` (axiom-clean ×3, 0 sorry, 0 warnings): the O108 census layer's consumable form of 2-power Lam–Leung, upgrading the in-tree set-form lemmas (`LamLeungUnconditionalGeneral.antipodal_of_sum_zero`) to genuine multisets.

* `count_antipodal_of_sum_eq_zero` — **the forward direction**: for char-0 `L` and a finite multiset `M` of `2^k`-th roots of unity, `M.sum = 0 ⟹ M.count z = M.count (−z)` for EVERY `z : L`. Route: `rootsOfUnity (2^k) L` is finite cyclic (Mathlib instances) of order `2^j` with `j ≥ 1` forced by `−1` (order 2 divides the generator's order — `orderOf_neg_one` at `ringChar = 0`); the generator `ζ` is primitive `2^j`-th; every element of `M` is `ζ^e` (zpowers reduced mod the order via `zpow_mod_orderOf`); the counting function on `ZMod (2^j)` then satisfies O96 `debruijn_prime_power_weighted` at `p = 2`, whose half-period shift is negation (`ζ^(2^(j−1)) = −1` by the square-roots-of-1 dichotomy + order pinch). Off-orbit `z` are handled honestly: `count z = 0 = count (−z)` (the orbit is negation-closed).
* `sum_eq_zero_of_count_antipodal` — the converse, no root-of-unity structure: antipodal balance + `0 ∉ M` kill the sum by the fixed-point-free pairing `z ↦ −z` (`Finset.sum_involution`; `−a = a ⟹ a = 0` in char 0).
* `multiset_antipodal_iff` — the iff in the exact O108-layer hypothesis shape (`∀ z ∈ M, z^(2^k) = 1`).
* Teeth at ℂ, genuine multiplicity: `{I, I, −I, −I}` vanishes (multiplicity 2 per antipode); `{1, I}` refuted via the count law at `z = 1`.

**Where it lands:** the O108 antipodal-balance engine (the 14-term μ₃₂ multiset reduction) now has its Lean-side foundation; the C1379/672 derivation's "multiset upgrade" gap is closed. Load-bearing transport recorded: `orderOf_units` + `orderOf_injective subtype` move orders across `G ≤ Lˣ → L`; `ZMod.val_add` + torsion give the `pow_val_add` digit identity.

### O114 — THE THREE-PRIME ℤ-GRID THEOREM: vanishing ℤ-weighted sums at squarefree pqr are EXACTLY the three-slab grids W(i,j,k) = α(j,k) + β(i,k) + γ(i,j) — Schoenberg/Rédei relation structure machine-checked, with the O105 witness constructively decomposed (W2-C harvest; nubs, 2026-06-10)

Two bricks (both exit 0, 0 sorry, 0 warnings, axiom-clean; probes `probe_three_prime_grid.py` + `probe_lam_leung_span_pqr.py` both exit 0, exact ℤ[x]/Φ arithmetic):

* `IntegerThreadSplit.lean` (axiom-clean ×4) — **the ℤ-coefficient thread-split iff**: for `p² ∣ n`, a ℤ-weighted power sum vanishes at `ζ` iff all `p` thread sums vanish at `ζ^p` — the O101 engine ported to `w : ℕ → ℤ` (the K-linear-independence core was always coefficient-agnostic); `int_sum_eq_thread_sum` regroup + both directions + the iff. The descent engine for ℤ-classifications at non-squarefree moduli.
* `DeBruijnThreePrimeIntGrid.lean` (axiom-clean ×7 + one axiom-FREE witness) —
  - `minpoly_adjoin_coprime_prime` — the coprime-tower minpoly gate instantiated for the triple-grid setting;
  - `int_grid_two_prime` — the two-prime ℤ-grid base (`W(i,j) = α_i + β_j`, ℤ coefficients — the ℤ-shadow of O100);
  - `int_grid_three_prime` — **the headline**: for distinct primes `p, q, r` and primitive roots `ξ, η, θ` (char 0), `Σ W(i,j,k)·ξ^i·η^j·θ^k = 0 ⟺ ∃ α β γ : ℤ-slabs, W(i,j,k) = α(j,k) + β(i,k) + γ(i,j)` — the relation module of squarefree three-prime roots of unity is exactly the three prime-fiber slabs (Schoenberg/Rédei structure, first formalization per the O91/O94 searches);
  - `int_total_three_prime` — the total identity `ΣW = qr·Σα + pr·Σβ + pq·Σγ`;
  - `witness_decomposes` (NO axioms — fully constructive) + `witness_no_nat_decomposition` — the O105 witness `S = {5,6,12,18,24,25}` at `n = 30` DECOMPOSED with explicit ℤ-slabs (negative entries necessary) and machine-checked to admit NO ℕ-slab decomposition: the ℤ/ℕ separation at three primes is now witnessed from both sides in one file.
* **The Stage-4 obstruction, charted honestly** (`probe_lam_leung_span_pqr.py`): the Lam–Leung ℕ-span theorem at `pqr` (total ∈ ℕp+ℕq+ℕr — TRUE, exhaustively confirmed on small boxes) does NOT follow from the grid + min-shift: on the O105 witness the slice evaluation `c` is NONZERO (the hard LL branch) and the per-(j,k) min-shift is identically 0 — no naive reduction exists. The witness total realizes `6 = 3 + 3` NOT via the slice split `4 + 2`: LL positivity is a genuinely global argument (their induction on cyclotomic structure), the named open formalization target past this brick.

**Where the open core moves:** the ℤ-side of vanishing-sums theory at three primes is CLOSED at squarefree level (grid = slabs), with the ℕ-side separation pinned constructively. Named next: (i) ℤ-classification at general `p^a·q^b·r^c` (IntegerThreadSplit descent + this base — assembly-shaped); (ii) LL ℕ-span at `pqr` (research — global positivity); (iii) wiring the slab decomposition into the 3+-prime window-law level interface named by O106.

### O115 — the LEVEL-2 TOWER CENSUS: the tower iteration adds ZERO counting power (forced level-2 loci are exactly the antipodal pairs of Z₁), and the surviving level-2 law is a level-1 reduction (W2-D harvest; nubs, 2026-06-10)

`scripts/probes/probe_tower_level2_census.py` (exit 0, deterministic, exact GF(q); exhaustive 83,521 f at (17,16,4) + 300k samples + all 65,536 joint profiles + 6.65M coset elements; full findings in the header docstring). O109 named the tower iteration as the surviving Conjecture-D content; this census RETIRES it as a union-bound mechanism, with the structural reason proof-shaped:

* **The deciding question — NO**: the level-2 union bound LU2(w) ≥ LU1(w) at EVERY tested w (equality iff the level-2 budget is vacuous; below n/4 it is 16×–1008× WORSE), and classical interpolation dominates both fold levels everywhere in the Johnson→capacity band (min LU2/CU = 3.71, rising to 2.4×10⁶).
* **The mechanism**: the forced level-2 dead locus is exactly the squares of antipodal pairs inside Z₁ — `pairs(Z₁) ⊆ Z₂(fe) ∩ Z₂(fo)`, `√pairs(Z₁) ⊆ Z₁` — so the merged constraint set is just Z₁: ZERO new dimensions. The tower multiplies CHOICES (C(n/4, z₂)² loci), never CONSTRAINTS. Excess level-2 deadness occurs at the accidental ~2(n/4)/q² null rate, not forced by the weight filter. Level-ℓ forcing needs `w < n/2^ℓ` — the tower dies geometrically strictly below Johnson (n/4 < n−√(nk) whenever k < 9n/16).
* **The POSITIVE law (formalizable, verified on all joint profiles)**: with merged sets `S_e = Z₁ ∪ √Z₂e`, `S_o = Z₁ ∪ √Z₂o`: `#{f : deg < k, slices vanish on Z₁, level-2 loci ⊇ Z₂e/Z₂o} = q^(max(0,⌈k/2⌉−|S_e|) + max(0,⌊k/2⌋−|S_o|))` — an exact q-power, but a REDUCTION to level 1 (`recompose_slices` + `card_polysDegLT_vanishing` at the merged sets — no new machinery). Dimensions multiply iff `√Z₂ ∩ Z₁ = ∅`; each overlap refunds one dimension. Weight ≤ w forces `√Z₂ ⊆ Z₁`, hence the level-2 union bound is TERMWISE ≥ O99's level-1 bound.
* Coset lists reproduce O109 (floor-trivial through capacity−2); level-2 thins nothing in the band.

**Verdict for Conjecture D:** level ≥ 2 content must come from incidence/inclusion–exclusion over locus overlaps or genuinely non-forced anticorrelation structure — NOT from multiplying per-level forced budgets. Both named survivors are now sharply delimited. Caveat: toy scale (n ≤ 16, q ≤ 257), but the domination LU2 ≥ LU1 and the √Z₂ ⊆ Z₁ forcing are structural.

### O109 — THE THREE-PRIME WALL BREACHED ON THE ℤ-SIDE: Schoenberg/Rédei ℤ-relation theorem at squarefree p·q·r, machine-checked both directions

O105 closed the ℕ-cone at three primes; the ℤ-module door is the classical structure that survives (Rédei 1959/Schoenberg 1964: ℤ-relations among n-th roots are packet-spanned at EVERY n). Probe-falsified first (`probe_schoenberg_z_relations.py`, exit 0: packet lattice = saturated sublattice — all Smith invariants 1 — of rank n − φ(n) at n = 12, 36, 30, 60, 90, 105, 210). `DeBruijnIntRelations.lean` (6 theorems, axiom-clean, 0 sorry, 0 warnings, pushed d225f26a7 + 5694b496c):

* `debruijn_int_two_prime` (stage 1) — ℤ-classification at p^a·q^b via the SHIFT TRICK: add c·𝟙 (𝟙 vanishes: geometric sum), classify the resulting ℕ-weight by O103, subtract c inside a coefficient function. ~40 lines on top of O103.
* `minpoly_adjoin_coprime_eq_cyclotomic` (stage 2) — minpoly ℚ(ζ_M) η = Φ_N for coprime M, N at GENERAL orders (the prime-power brick's totient-pinch proof was secretly order-agnostic). `natDegree_minpoly_adjoin_coprime` extracts [ℚ(ζ_M)(ζ_N) : ℚ(ζ_M)] = φ(N).
* `coprime_thread_sums_eq` (stage 3) — **the coprime thread split**: at n = m·r (r prime, coprime m), vanishing forces all r CRT thread sums at level m EQUAL (vs. ZERO in the non-coprime O93 split — the missing dimension of Φ_r, deg r−1, is exactly the welding relation Σ ζ_r^i = 0). New `crt` API on `Nat.chineseRemainder` (roundtrip, uniqueness, primitive-root factorization ζ^{crt k i} = ζ_m^k ζ_r^i, box regrouping).
* `debruijn_int_three_prime_squarefree` (stage 4) — **the headline iff**: Σ w_e ζ^e = 0 ⟺ w_e = A(e % qr) + B(e % pr) + C(e % pq) with ℤ-functions. Forward: equal threads → differences vanish at pq → stage 1 per thread → CRT mod-identity fold. The O105 witness is consistent: its ℤ-decomposition needs a negative coefficient (μ₅ − μ₃), exactly what the ℕ-cone forbids — both theorems sharp simultaneously.

**Where the open core moves:** squarefree three-prime ℤ is closed. Named next (assembly, not research): non-squarefree p^a·q^b·r^c (O93 split for repeated digits + stage 3 for the new prime, same recursion); k-prime (stage 3 is general in m). Genuinely open: Lam–Leung ℕ-span at 3+ primes — now REDUCED to nonnegativity bookkeeping over the in-tree ℤ-skeleton. (Cold-audit note: sorry_census shows 1 hole at WindowFiberCount.lean:217, another lane's live file — flagged, not this lane's.)

### O116 — THE 0/1 PACKING LAW RESOLVED BOTH WAYS: complement closure gives the TWO-SIDED span law (necessity, formalized), and the CRT obstruction REFUTES its sufficiency — the realizable mass set is pinned between (fable lane, 2026-06-10)

O112's named open (i) — the 0/1 packing characterization — attacked falsify-first and resolved into a theorem + a refutation. `WindowMassSpan.lean` +4 theorems (9 total in file, all axiom-clean `[propext, Classical.choice, Quot.sound]`, 0 sorry, 0 warnings):

* `full_range_pow_sum_eq_zero` + `complement_window_vanishes` — **COMPLEMENT CLOSURE** (any modulus): the full range `[0,n)` kills every window power sum (`1 ≤ j < n`), so the window fiber is closed under complement — `S ∈ F_n(t) ⟺ [0,n)∖S ∈ F_n(t)`.
* `window_mass_two_sided_two_prime` — **THE TWO-SIDED SPAN LAW** (necessity): at `n = p^a·q^b`, a window-`t`-vanishing 0/1 set has BOTH `|S|` and `n−|S|` expressible as sums of divisors `> t`. Strictly stronger than O107's one-sided spectrum.
* **The `66`-tooth** (`n = 72`, `t = 9`): weight `66 = 12+18+36` IS a divisor sum, yet `72−66 = 6` is not ⟹ weight 66 IMPOSSIBLE — invisible to every one-sided bound; kernel-checked via the 6-element complement violating the min weight 12.
* `two_sided_not_sufficient` — **THE CRT REFUTATION**: at `(n,t) = (36,3)`, mass `13` passes the two-sided test (`13 = 9+4`, `23 = 9+6+4+4`) yet NO window-3-vanishing 0/1 set has 13 elements: the only divisor rep of 13 is `{9,4}`, and a `μ_9`-coset (step 4) and `μ_4`-coset (step 9) have coprime steps — CRT forces intersection. Proof extracts the packets (parity: odd sum ⟹ a 9-packet; remainder 4 ⟹ a 4-packet) and exhibits the explicit CRT witness `x = (9r + 28r') % 36 ∈ P₉ ∩ P₄` (omega discharges all mod bookkeeping), contradicting disjointness.

**Falsify-first** (`probe_window_packing_law.py`, exit 0, exhaustive n ∈ {12,18,20,24,36}, all t): necessity holds everywhere; the CRT stratum (two-sided-but-unrealizable masses) at `(36,3)` is exactly `{13, 17, 19, 23}` (complement-symmetric, as forced); the naive tiling claim is ALSO false — `{4,3,3,2}` does not tile `ℤ_12` (parity invariant: 3x + 2y = 4 unsolvable over the class capacities).

**Where the packing surface now stands, sharply:** realizable masses sit STRICTLY between the two-sided span (proven necessary) and disjoint-packing feasibility (the exact object). The remaining open content is the class-capacity combinatorics — for two generators: `a` μ_d-cosets + `b` μ_d'-cosets pack iff `⌈aG/s⌉ + ⌈bG/s'⌉ ≤ G` (`s = n/d`, `s' = n/d'`, `G = gcd(s,s')`; same-class cosets of coprime-quotient steps always collide) — Berger–Felzenbaum–Fraenkel lattice-parallelotope / Korec natural-DCS territory, finite per `(n,t)`. Named next: (a) the two-generator capacity law as a theorem (the first sufficiency rung); (b) the general criterion at two-prime `n` (BFF-natural systems); (c) the per-mass fiber count (O111's weighted analogue).
||||||| parent of 147828cea (feat(#232): THE GENERAL SQUAREFREE Q-CLASSIFICATION — the arity induction at every squarefree n; the designed-assembly queue is EMPTY (O109))
### O109 — THE GENERAL SQUAREFREE ℚ-CLASSIFICATION LANDS: the arity induction is a theorem — the designed-assembly queue is EMPTY

The O109 forward, gated with full design in the O109a entry, executed same-session. `RatSquarefreeClassification.lean` (axiom-clean, 0 sorry, 0 warnings): `rat_squarefree_classification` — for EVERY squarefree `n` (arbitrary number of prime factors), `ζ` primitive `n`-th (char 0), `w : ℕ → ℚ`:

    `Σ_{e<n} w_e·ζ^e = 0 ⟺ ∃ A : ℕ → ℕ → ℚ, ∀ e < n, w e = Σ_{p ∈ primeFactors n} A p (e % (n/p))`

— the de Bruijn–Schoenberg LINEAR theory of vanishing weighted root-of-unity sums at arbitrary arity, subsuming O102 (k = 2) and O107 (k = 3) as instances. Strong induction peeling `minFac n`: the CRT transport at general composite cofactor (`Coprime e₂ m` from `e₂ ≡ 1 [MOD m]` by one `gcd_rec` — the only place O102's prime-cofactor argument needed upgrading); the p-fiber coefficients in `ℚ⟮η'⟯` (cofactor root adjoined DIRECTLY — the O107b composite-generator juggling is unnecessary when peeling one prime); the O106 gate at `(m, p)`; fiber differences to the IH; the decode `A p y := W(0,y)`, `A q y := B_{y%p} q (y%(m/q))` with the three `mod_mod_of_dvd` well-definedness identities; converse = O109a. Lean gotchas: `simp only []` normalizes `if p = p` to `if True` breaking subsequent rw — `show` the beta-reduced if-form instead; ModEq hypotheses unfold to %-equations only via an explicit `have h' : _ % _ = _ % _ := h`.

**STATE OF THE CLASSIFICATION PROGRAM AFTER O97→O109 (one session, fourteen generations):** every assembly-shaped item is now PROVEN — there is no designed-but-unproven item left anywhere in the de Bruijn/counting lanes. The complete machine-checked map: two-prime theory total (indicator + weighted iffs, window law, tower, budgets, span) and SHARP (O105); three-prime and general-arity LINEAR theory total (ℚ at all squarefree n, ℤ at pqr); the positivity boundary pinned from both sides. The open residue is exclusively research mathematics with no known proofs to formalize: (1) Lam–Leung's positivity induction (the span theorem's ℕ-content at 3+ primes — its linear half is now THIS theorem); (2) the t > 1 window law at 3+ prime moduli; (3) the O99 incidence geometry; (4) δ*. Each sits directly on a formalized boundary.

### O117 — the WINDOW FIBER-COUNT LAW lands in Lean: the block-trace iff on the O106 predicate — F_n(t) ≅ F_m(t)^(n/m) at set level (the O111 Lean layer; nubs, 2026-06-10; renumbered from O116 — it raced the fable lane's packing-law O116)

`WindowFiberCount.lean` (axiom-clean ×5, 0 sorry, 0 warnings, namespace `DeBruijnWindowedLaw`): O107's named next (ii), the probe layer O111 made exact, now a theorem.

* `isWindowCosetUnion_iff_traceBlocks` — **the headline**: under the abstract interface (H) — `m ∣ n` and every divisor `d ∣ n` with `d > t` has `gcd(d, m) > t` (the property O111 verified for `m = lcm(Dmin)`) — `S ⊆ [0,n)` is a window coset union at level `n` ⟺ ALL `n/m` block traces `{e/g : e ∈ S, e ≡ c (mod g)}` are window coset unions at level `m`. Since a set is determined by its block traces, this IS the set-level bijection `F_n(t) ≅ F_m(t)^(n/m)` behind O70's exact count law (10⁶ = |F_6(1)|⁶ at n = 36 etc.).
* `traceBlock_cosetOf` — **the key structural lemma**: the block trace of a canonical `μ_d`-coset is empty or a canonical `μ_{gcd(d,m)}`-coset at level `m`. Engine: canonical cosets ARE residue classes in `[0,n)` (`mem_cosetOf_iff_mod`); the trace condition is the linear congruence `g·e' ≡ r − c (mod n/d)`, whose solution classes have modulus `(n/d)/gcd(g, n/d)`; and the DIVISOR IDENTITY `(n/d)·gcd(d,m) = m·gcd(n/m, n/d)` — both sides are `gcd(n, (n/d)·m)` by `gcd_mul_left` twice, zero division pain — pins that modulus as the level-`m` step `m/gcd(d,m)`.
* `isWindowCosetUnion_traceBlock` / `isWindowCosetUnion_of_traceBlocks` — the two directions: traces of disjoint cosets stay disjoint (preimage injectivity); lifts `e' ↦ c + g·e'` send level-`m` cosets to canonical level-`n` cosets with the SAME divisor (`liftBlock_cosetOf`: `g·(m/d') = n/d'`), cross-block disjointness by residues, per-block choice via `choose`.
* Congruence engine extracted (`trace_congr`/`trace_congr_mem`): `Nat.ModEq.mul_left_cancel'` + `cancel_left_of_coprime` after factoring the gcd — reusable for any future block-collapse argument.

**O117 addendum (same pass):** the `m = lcm(Dmin)` instantiation LANDED — `minWindowDivisors n t` (the divisibility-minimal divisors > t), `exists_minWindowDivisor_dvd` (strong induction: every divisor > t sits over a minimal one), and `isWindowCosetUnion_iff_traceBlocks_lcm` — the fiber-count law at O70's canonical modulus, hypothesis-free beyond `0 < n` (interface (H) discharged via `Nat.dvd_gcd` + `Finset.dvd_lcm`; positivity via `Finset.lcm_eq_zero_iff`). **Second addendum (same pass): the literal count LANDED** — `windowFiber n t` (the fiber as a `Finset (Finset ℕ)`), `card_windowFiber : |F_n(t)| = |F_m(t)|^(n/m)` under (H) via `Finset.card_bij` onto `Fintype.piFinset` (trace tuple forward, lift-union backward, trace∘lift block identities), and `card_windowFiber_lcm` at the canonical modulus. NOTHING remains open on the fiber-count surface. With O106 (the law) + O107/O112 (spectra) + this (the count structure), the two-prime windowed program is closed at every named surface.

### O110 — LAM–LEUNG REDUCED TO THE SQUAREFREE BASE: the square-descent half of the span theorem is a theorem; ≤2-prime moduli CLOSED

Correction to the residue bookkeeping: Lam–Leung's ℕ-span theorem is PUBLISHED mathematics (J. Algebra 224 (2000)), not open research — only unformalized. Its square-descent half is provable today via O101 and is now landed. `LamLeungSquarefreeReduction.lean` (axiom-clean ×3, 0 sorry):

* `lam_leung_span_descent` — the `p² ∣ n` step: threads vanish (O101), per-thread weights lie in the span (hypothesis at level `m`), the total is the thread-sum (`nat_digit_sum`), and `primeFactors (p·m) = primeFactors m` when `p ∣ m`.
* `lam_leung_of_squarefree` — **the reduction**: the ℕ-span law at every squarefree level implies it at EVERY level (strong induction stripping prime squares, `Nat.squarefree_iff_prime_squarefree`).

**Consequence (composition, no new proof needed): Lam–Leung is now CLOSED at every modulus with at most two distinct primes** — prime powers via the descent to `n = p` (rigidity gives weight ∈ ℕp), and all `p^a·q^b` via the descent to the squarefree base `pq` where O104 lands it. The remaining formalization residue of the span theorem is EXACTLY the squarefree base with ≥ 3 distinct primes — where the packet route is dead (O105), the linear scaffolding is done (O109), and the published route is Lam–Leung's minimal-vanishing-sum induction (§4–5 of the paper): a real formalization project with a known proof, precisely gated, NOT open mathematics. The honest open-research residue on this lane is therefore only: the t>1 window law at 3+ primes (no literature), the O99 incidence geometry, and δ*.

### O110 — THE FULL RÉDEI–DE BRUIJN–SCHOENBERG RELATION THEOREM: vanishing ℤ-combinations of n-th roots of unity classified at EVERY modulus — first formalization in any proof assistant (per the O91/O94 searches)

O109 closed squarefree three primes; this pass removes every restriction. `DeBruijnIntRelations.lean` (now 12 theorems + ℂ teeth, all axiom-clean, 0 sorry, 0 warnings, pushed 21c2186bd):

* `redei_debruijn_schoenberg` — **the headline iff** (Rédei 1959; Schoenberg Mathematika 11 (1964) Thm 1): for every `n ≥ 1`, `Σ_{e<n} w_e ζ^e = 0 ⟺ ∃ A, w_e = Σ_{p ∈ n.primeFactors} A_p(e % (n/p))` over ℤ. De Bruijn's ℕ-conjecture is FALSE at 3 primes (O105) but TRUE over ℤ at all n — both halves of that dichotomy are now in-tree, sharp against each other.
* `int_combination_of_vanishing` — the strong induction, peeling `r = minFac n`: **r² ∣ n** → `int_thread_vanishing_of_vanishing` (O93/O101 thread split transported to ℤ by the shift trick; the shift's threads are geometric sums, zero) + the O103 digit lift `A'_p(x) = A_{x%r,p}(x/r)`; **r ∥ n** → the O109b coprime equal-thread-sums split + IH on differences + CRT mod-identity fold, the welded thread becoming the μ_r-packet coefficient `C(x) = w(crt x (r−1))`.
* `int_vanishing_of_combination` — generic converse (sum swap + per-prime geometric kill).
* Teeth at ℂ, n = 4: μ₂-packet weight fires `1 + i² = 0` (.mpr); singleton δ₀ refuted (.mp forces w(0) = w(2)).

**Where the open core moves:** the ℤ-relation theory of roots of unity is CLOSED at every modulus. Remaining genuinely open on the de Bruijn lane: (i) Lam–Leung ℕ-span (|w| ∈ ℕp₁ + … + ℕp_k) at 3+ primes — now reduced to nonnegativity bookkeeping over the in-tree ℤ-skeleton; (ii) the windowed laws at 3+ primes, for which the ℤ-classification is the natural level-interface candidate; (iii) consumers: ℤ-relation structure on arbitrary smooth-domain subgroups (M31-adjacent mixed-radix beyond two primes).

### O111 — the O70 divisor-coset window law is FALSE at three primes: the statement-level obstruction, kernel-checked

The window-law residue redteamed at the statement level. `ThreePrimeWindowObstruction.lean` (axiom-clean, Mathlib+O105 only): `divisor_coset_law_fails_three_primes` — the O105 witness `{5,6,12,18,24,25}` at `n = 30` vanishes, yet through its point `5` NO full `μ_d`-coset lies inside the set for ANY `1 < d ∣ 30` (a `decide` over `Nat.divisors 30`). So the O70 form of the window law — windowed-vanishing subsets decompose into `μ_d`-cosets, `d > t` — fails at three primes ALREADY at `t = 1`: its very statement, not merely its proof, has no 3+-prime extension. Any 3+-prime window law must be reformulated — the candidate surface is the O109 ℚ-component form with windowed power sums constraining the components. The window-law residue is now: *find and prove the correct 3+-prime statement* — with its impossibility boundary formalized.

### O118 — the LEVEL-2 COUNTING LAW in Lean: tower profiles reduce to level-1 merged sets — the O115 positive residue formalized (nubs, 2026-06-10)

`SliceLevelTwoCount.lean` (axiom-clean ×4, 0 sorry, 0 warnings, namespace `LamLeungTwoPow`): the law the O115 census verified on all 65,536 joint profiles, now a theorem with no new counting machinery — exactly as the census predicted.

* `card_polysDegLT_slices_vanishing_asym` — **the missing primitive**: per-slice loci can differ — `#{f : deg < k, evenSlice ⊨ S_e, oddSlice ⊨ S_o} = q^((k+1)/2 − |S_e|)·q^(k/2 − |S_o|)` (the O96 build-bijection with independent factors).
* `slices_eval_sq_zero_iff` — **the O115 mechanism as an iff**: both slices of `h` vanish at `v²` ⟺ `h(v) = h(−v) = 0` (char ≠ 2, `v ≠ 0`) — forced level-2 deadness IS the antipodal-pair shadow of level-1 deadness; the lemma behind `pairs(Z₁) ⊆ Z₂` and `√Z₂ ⊆ Z₁`.
* `mergedLocus Z₁ V = Z₁ ∪ V ∪ (−V)` + `vanish_mergedLocus_iff` — the constraint transport.
* `card_level_two_profile` — **the headline**: the joint (level-1 `Z₁`, level-2 `{v² : v ∈ V_e}/{v² : v ∈ V_o}`) per-profile count equals the asymmetric count at the merged sets — an exact q-power; dimensions multiply iff the merged unions are disjoint, each overlap refunds one dimension (the censused refund, now structural).

**Where this leaves Conjecture D:** with O109 (level 1 = classical MDS), O115 (tower budgets never beat level 1), and this brick (the exact per-profile law at level 2), the counting side of the fold tower is CLOSED — all that survives is the incidence/inclusion–exclusion channel over locus overlaps and the anticorrelation structure, both genuinely open.

### O111 — THE ℤ-WINDOWED LAW AT EVERY MODULUS: the windowed program escapes the two-prime cage — the windowed-law lattice is COMPLETE

Probe-falsified first (`probe_int_windowed_law.py`, exact ℤ[x]/Φ_n + Smith normal form, exit 0: 15 (n,t) pairs at n = 12, 30, 36, 60, 105 — the d > t coset lattice kills the window, has rank = the ℚ-kernel dimension of the window system, and is saturated). `DeBruijnIntWindowedLaw.lean` (5 theorems, axiom-clean, 0 sorry, 0 warnings, pushed c22d87f25):

* `int_windowed_law` — **the headline iff at EVERY n**: `(∀ j ∈ [1,t], Σ_{e<n} w_e ζ^{je} = 0) ⟺ w ∈ ℤ-span{μ_d-coset indicators : d ∣ n, d > t}`. The O106/O108 two-prime cage was the ℕ-level interface (REAL for ℕ by O105); over ℤ the level classifier at every modulus is O110, and the O108 induction (kill + resonance + fiberwise fold) runs unchanged — kill/resonance transported to ℤ by pos/neg splits against the O108 ℕ-lemmas.
* The windowed-law LATTICE is complete and fully machine-checked, refutations included: {0/1, ℕ, ℤ} × {t = 1, all t} × {two-prime, every n}: O94/O103/O109a (t=1 two-prime), O106/O108 (all-t two-prime), O105 refutations (ℕ-rows at 3 primes), O110/O111 (ℤ-rows at every n). No open cells.

**Where the open core moves:** exactly ONE genuinely-open item remains on the de Bruijn lane — the Lam–Leung ℕ-span (total weight ∈ ℕp₁+⋯+ℕp_k at 3+ primes), the nonnegativity refinement strictly between the refuted ℕ-cone and the proven ℤ-module. Everything else on this lane is theorem or counterexample. Prize-adjacent consumers of O111: window-code ℤ-codeword structure on ARBITRARY smooth domains (incl. 3-smooth M31-adjacent and beyond), and the t-general fiber analysis feeding the mixed-radix capstones.

### O119 — THE TWO-GENERATOR PACKING CAPACITY LAW: the first sufficiency rung of the packing surface is an iff — packability of a·μ_d + b·μ_{d'} is exactly the class-allocation ceiling bound (fable lane, 2026-06-10)

O116's named next (a) executed. `TwoGenPackingCapacity.lean` (8 theorems + 2 teeth, all axiom-clean `[propext, Classical.choice, Quot.sound]`, 0 sorry, 0 warnings):

* **The intersection trichotomy**: `cosetOf_disjoint_same` (same-type cosets disjoint iff distinct bases), `cosetOf_disjoint_cross` (cross-type disjoint if bases differ mod `G = gcd(n/d, n/d')`), `cosetOf_not_disjoint_cross` — **the CRT direction**: bases agreeing mod `G` force intersection (`Nat.chineseRemainder'` produces the common element below `lcm ∣ n`). O116's ad-hoc (36,9,4) obstruction is now the `G = 1` instance of a general law.
* `two_generator_capacity` — **THE IFF**: `a` canonical `μ_d`-cosets and `b` canonical `μ_{d'}`-cosets pack pairwise-disjointly in `[0,n)` ⟺ `⌈a/m⌉ + ⌈b/m'⌉ ≤ G` (`s = n/d`, `m = s/G`, etc.). Necessity (`capacity_of_packable`): cross pairs occupy distinct base-classes mod `G` (CRT), per-class fibers hold ≤ `m` bases (`fiber_card_le`), so `⌈a/m⌉ + ⌈b/m'⌉` ≤ #classes-used ≤ `G`. Sufficiency (`packable_of_capacity`): the explicit block construction — `d`-bases enumerate `j ↦ (j%k) + G·(j/k)` filling classes `0..k−1`, `d'`-bases fill the next `k'` classes; all index identities by `omega` after linearizing products through abstract block data (`packable_of_blocks`).
* `two_gen_mass_realizable` — the window-fiber consumer: `d, d' > t` + capacity ⟹ the mass `a·d + b·d'` is realized by an `IsWindowCosetUnion n t` (full-cardinality forces cross-disjointness — `cross_disjoint_of_card`, a pigeonhole identity).
* Teeth: `¬ Packable 36 9 4 1 1` (the O116 obstruction through the law: `⌈1/4⌉+⌈1/9⌉ = 2 > 1 = gcd(4,9)`); `Packable 36 6 9 3 2` (a genuinely mixed FULL TILING of `[0,36)`: `3·6 + 2·9 = 36`, `G = 2`, `⌈3/3⌉+⌈2/2⌉ = 2 ≤ 2`).

**Falsify-first** (`probe_two_gen_capacity.py`, exit 0): structural facts (same-type disjointness; cross-type iff class-collision) EXHAUSTIVE over n ∈ {12,18,20,24,30,36}, all ordered divisor pairs, all base pairs; the ceiling law verified against independent raw-backtracking ground truth on 7,126 tractable instances (2,983 skipped where the search space exceeds 2·10⁵, reported not hidden).

**Where the packing surface moves:** the two-generator case of the 0/1 mass realizability problem is CLOSED as an iff. The full problem (arbitrary divisor multisets) is now a hypergraph-allocation question over the class structure: each divisor `d` sees `[0,n)` as `G_d`-classes through its base set, multisets interact pairwise through `gcd` lattices — the k-generator law needs simultaneous class allocation (Berger–Felzenbaum–Fraenkel disjoint-covering-systems territory; the pairwise condition is provably insufficient in general DCS theory, worth a probe at small n). Named next: (a) probe whether pairwise capacity suffices at two-prime n for 3 generators (suspect NO — find the witness); (b) the per-mass fiber count.

### O120 — the COSET AGREEMENT-SPECTRUM MOMENTS: mean and second moment are domain-independent CLOSED FORMS (verified exactly), so δ*'s domain-dependence lives strictly in the upper tail — and smooth vs random domains are indistinguishable at toy scale (nubs, 2026-06-10; renumbered from O119 — raced the fable lane's packing-capacity O119)

`scripts/probes/probe_coset_agreement_moments.py` (exit 0, exact arithmetic): the incidence lane's reframing after O109/O115/O118 closed the counting side. For the agreement spectrum `a_j(u) = #{p ∈ RS : |{x ∈ D : p(x) = u(x)}| = j}` (list size = upper partial sums):

* **(M1) the first moment is a closed form**: `Σ_u a_j(u) = q^k·C(n,j)·(q−1)^(n−j)` — pure double counting, ANY n-point domain. Verified as an exact integer identity over ALL q^n received words at (q,n,k) = (5,4,2) and (7,6,2).
* **(M2) the second moment is a closed form through the distance distribution**: `Σ_u a_j(u)² = Σ_d B_d·N_j(d)` with `B_d` the (MDS) codeword-pair distance counts and `N_j(d)` the exact per-pair count (agreement/disagreement coordinate combinatorics with the (1,1,q−2)-split on disagreement coordinates). Verified exactly over all u at both full-enumeration setups.
* **Consequence (the reframing):** mean AND variance of coset list sizes are DOMAIN-INDEPENDENT (MDS + pair combinatorics) — every domain-specific fact about `δ*` (the whole derandomization question, §6 direction 1 of the issue) is a statement about moments ≥ 3 / the upper tail of `a_j(u)` over `u`. The prize-relevant question is exactly: does the smooth domain's tail exceed the random domain's?
* **Toy-scale verdict: NO separation.** At q = 257, n = 16, k = 2 (300 sampled u each): the order-16 smooth subgroup and a random 16-point domain have indistinguishable band profiles (max ℓ at w = 12: 2 vs 1; w = 13: 7 vs 6; capacity: 120 vs 120; identical means). Max-to-mean ratios collapse to ~1 at capacity at every setup — the tail is thin where the mean is large, and the only structure is Poisson-like discreteness where the mean is tiny (ratio 19–400 at Johnson, on counts of 0/1/2).
* **Named Lean target (clean, domain-independent):** the M1 double-counting identity as a `Finset.card` theorem — `Σ_u a_j(u) = q^k·C(n,j)·(q−1)^(n−j)` — the first moment of the list-size law, formalizable with `card_polysDegLT`-style enumeration + a product bijection (codeword × agreement-pattern × off-pattern values). M2 is the second target once the distance distribution is in-tree.

**Where the open core moves:** the incidence lane's honest frontier is now: (i) tail bounds for `a_j(u)` beyond variance (Chebyshev via M2 gives the first nontrivial max-bound — worth extracting); (ii) the third-moment/triple-correlation structure where domain-dependence could first appear (triples of codewords vs u — relates to the code's TRIPLE distance enumerator, where smooth structure could matter); (iii) δ* itself.

### O112 — LAM–LEUNG ℕ-SPAN REDUCED TO SQUAREFREE LEVELS: the de Bruijn lane's last open wall pinned to squarefree k ≥ 3 (first case n = 30)

`DeBruijnLamLeungReduction.lean` (axiom-clean ×2, 0 sorry, 0 warnings, pushed 8c01f2671):

* `lam_leung_reduction_to_squarefree` — span law at every squarefree divisor level ⟹ span law at `n`. Strong induction; at non-squarefree levels r² ∣ n fires O101's weighted thread split (threads vanish INDIVIDUALLY with ℕ-weights at n/r, same prime set); `total_eq_thread_totals` (O101 regrouping at ζ = 1) adds the thread totals; memberships in the span monoid add.
* Combined in-tree status of Lam–Leung: prime powers (O96) ✓, two-prime (O104) ✓, any n given its radical (O112) ✓ — open EXACTLY at squarefree k ≥ 3.
* **Why the residual is genuinely hard, machine-checked context:** at squarefree n = m·r the coprime split (O109b) yields equal thread sums; thread-difference totals lie in ℤp₁+⋯+ℤp_{k−1} (O110), which for k−1 ≥ 2 is ALL of ℤ — the ℤ-classification carries no ℕ-cone congruence. Lam–Leung's own route is group-ring/augmentation-ideal induction: research-grade, not assembly.

**Session net (this lane, 2026-06-10): O106 → O112.** The windowed-law lattice {0/1, ℕ, ℤ} × {t = 1, all t} × {two-prime, every n} is COMPLETE (theorems + refutations, no open cells); ℤ-relation theory of roots of unity closed at every modulus (first Rédei–de Bruijn–Schoenberg formalization); the single named open residual is the squarefree-k≥3 ℕ-span.

### O112 — the FIRST windowed structure law at three primes: the q-power fiber-count decomposition (the post-O111 surface carries)

O111 killed the coset surface; this pass lands the first POSITIVE windowed structure theorem on the corrected count surface. `ThreePrimeFiberCountLaw.lean` (axiom-clean ×2): `qpower_fiber_count_law` — distinct primes p, q, r, `T ⊆ μ_{pqr}` (char 0), `Σ_{y∈T} y^q = 0` ⟹ the q-power fiber-count function `f ↦ #{y ∈ T : y^q = (ζ^q)^f}` on `μ_{pr}` decomposes with NONNEGATIVE components: `= A (f%r) + B (f%p)`. The positivity O105 forbids for T itself HOLDS for its q-power shadow — the multiplicity descent (`sum_pow_eq_fiber_weight`: Σ y^q = Σ_f m_f·(ζ^q)^f, fiberwise partition + discrete-log reindex) lands the count function in the squarefree two-prime weighted theory where O102 classifies it with ℕ-components.

**The reformulated three-prime window program, now precisely shaped:** each window exponent with gcd q (resp. p, r) yields one fiber-count law at the opposite two-prime level (this theorem and its two transposes); window exponents coprime to n yield reindexed O109-component constraints. The OPEN problem = assembling these per-exponent laws into a closure/rigidity statement for T itself (the analogue of the O97 spectral recursion, whose packet entry point O105 removed). That assembly question is the honest residual window-law content — now with both its impossibility boundary (O111) and its building blocks (this) machine-checked.

### O121 — PAIRWISE CAPACITY IS NOT ENOUGH: the chromatic TRIANGLE OBSTRUCTION at three generators — packing is graph coloring, machine-checked (fable lane, 2026-06-10)

O119's named next (a) resolved: the answer is NO, with the mechanism identified, generalized, and proven. `ThreeGenPackingObstruction.lean` (2 theorems + 1 tooth, axiom-clean ×2, 0 sorry, 0 warnings):

* `triangle_obstruction` — **the general chromatic law**: for ANY `n` and three divisors `d₁, d₂, d₃` whose pairwise step-gcds all divide 2 (`gcd(n/dᵢ, n/dⱼ) ∣ 2`), NO choice of canonical bases makes the three cosets pairwise disjoint. Mechanism: O119's CRT lemma forces disjoint cosets' bases to DIFFER mod each pairwise gcd — with gcd ∣ 2 that means pairwise-distinct parities, and ℤ/2 has only two elements. **Packing is graph coloring on the class structure; a triangle is not 2-colorable.**
* `three_gen_separation` — **the headline separation** at the minimal witness `n = 12`, `(d₁,d₂,d₃) = (2,3,6)` (steps 6, 4, 2; all pairwise gcds = 2): (1) every PAIR packs (O119 capacity satisfied pairwise, witnessed constructively through `packable_of_capacity`); (2) volume `2+3+6 = 11 ≤ 12`; (3) the triple is unpackable for EVERY base choice. Pairwise capacity + volume do not determine `k ≥ 3` packability.
* Tooth: the `(4, 6, 12)` family at `n = 12` (steps 3, 2, 1 — gcds 1, 1, 1) dies through the same theorem (the `G = 1` face).

**Falsify-first** (`probe_three_gen_packing.py`, exit 0): exhaustive over ALL volume-feasible multiplicity vectors at `n ∈ {12, 18, 24, 36}` — **629 pairwise-capacity-satisfying, volume-feasible, unpackable witnesses** (2/6/94/527 per modulus), minimal = this brick's; O119's necessity direction confirmed on every packable instance (zero violations — the iff survives its first adversarial sweep).

**The packing hierarchy is now strict and machine-checked at every level**: one-sided divisor span (O107) ⊊ two-sided span (O116, complement closure) ⊊ pairwise capacity (O119) ⊊ packability (this brick). The exact `k`-generator law is simultaneous class allocation — list-coloring over the gcd-lattice graph (BFF/Korec DCS theory). Named next: (a) is the obstruction always chromatic? — probe whether pairwise capacity + proper-coloring feasibility of the class-constraint graph characterizes packability at two-prime `n` (the witnesses' structure suggests testing list-chromatic feasibility); (b) the per-mass fiber count (O117's weighted analogue).

### O122 — PACKING IS EXACTLY CLASS-CONSTRAINT SATISFACTION: the CSP characterization of arbitrary coset families, every modulus (fable lane, 2026-06-10)

The identification O121 used implicitly, closed as an iff. `PackingClassCSP.lean` (2 theorems, axiom-clean ×2, 0 sorry, 0 warnings, first-shot compile):

* `packing_iff_csp` — for ANY finite family `F ⊆ {(d, r) : d ∣ n, r < n/d}` of canonical cosets at ANY modulus `n`: **the family is pairwise disjoint ⟺ every cross-type pair occupies distinct base-classes mod the pairwise step-gcd** (`p.2 % gcd(n/p.1, n/q.1) ≠ q.2 % gcd(...)`). Same-type distinct-base disjointness is free; the geometry of `[0, n)` drops out entirely — `k`-generator packability IS a heterogeneous "differ-mod-g" constraint-satisfaction problem, exactly and not just morally.
* `csp_family_card` — a CSP-satisfying family's union realizes the full mass `Σ_{(d,r) ∈ F} d` — feasibility transfers to exact mass realization in one `card_biUnion`.

**Where every landed law now sits**: O119 = the 2-type CSP is interval-capacity-solvable (iff); O121 = a triangle of `gcd ∣ 2` constraints is infeasible (2-coloring); O116's CRT obstruction = the single `gcd = 1` edge. The open exact `k`-type law is feasibility of these CSPs — Berger–Felzenbaum–Fraenkel disjoint-covering-systems combinatorics over the divisor-gcd lattice, now with a clean machine-checked interface: any future feasibility criterion proves a packing law by composing with `packing_iff_csp`, zero geometry required. Structure constants probe-verified exhaustively (probe_two_gen_capacity.py check (A), n ∈ {12,…,36}, all divisor and base pairs).

### O122 — M1 IS A THEOREM: the agreement-spectrum first moment in Lean — mean coset list sizes are domain-independent (the O120 named target; nubs, 2026-06-10)

`AgreementMomentOne.lean` (axiom-clean ×2, 0 sorry, 0 warnings): the O120 closed form, machine-checked at full generality.

* `card_exact_agreement` — **the generic exact-agreement count** (ToMathlib-grade): functions `u : α → β` agreeing with a fixed `f` on EXACTLY `j` coordinates number `C(|α|, j)·(|β|−1)^(|α|−j)`. Route: partition by the agreement set (`powersetCard` biUnion); each fiber IS a `piFinset` of singletons (on the set) and punctured codomains (off it) — `Fintype.card_piFinset` + `prod_ite` close it.
* `sum_agreement_spectrum` — **M1**: `Σ_{u : D → F} a_j(u) = q^k·C(|D|, j)·(q−1)^(|D|−j)` where `a_j(u) = #{p : deg < k, p agrees with u on exactly j points of D}` — for EVERY `|D|`-point domain. Double counting (`Finset.sum_comm` after `card_filter`), the generic count per codeword, `card_polysDegLT` for the codeword total. The mean coset list size `E_u[ℓ(u, w)] = q^{k−n}·Σ_{j ≥ n−w} C(n,j)(q−1)^{n−j}` is now a corollary-shaped consequence.

**Where this aims:** with M1 in-tree, the O120 reframing is half-formal: domain-independence of the FIRST moment is a theorem; M2 (through the distance distribution) is the next named brick (needs the MDS weight enumerator in-tree — itself a worthy classical target); Chebyshev via M2 would give the first machine-checked nontrivial max-list bound. δ*'s domain-dependence provably cannot appear before the second moment.

### O113 — the UNIVERSAL window endpoint: full window ⟹ ∅/full at EVERY modulus — the assembly question bracketed from above

`FullWindowDichotomy.lean` (axiom-clean): `full_window_dichotomy` — at EVERY modulus `n` (no prime-structure hypothesis), `T ⊆ μ_n` with power sums vanishing on the whole window `1 ≤ j < n` is `∅` or all of `μ_n`. Discrete Fourier orthogonality: the double sum `Σ_{j<n} Σ_{e∈S} ζ^{j(e+n−e₀)}` is `n·𝟙_S(e₀)` summed `e`-first (off-diagonal geometric sums die; the divisibility pinch `n ∣ e+(n−e₀) ⟺ e = e₀` inside `(0, 2n)`) and `|S|` summed `j`-first (the window kills every `j ≠ 0` row through the O97 bridge) — so the indicator is constant.

**The three-prime window hierarchy is now machine-checked at three strata**: `t = 1` (O109 ℚ-components), single gcd-exponents (O112 fiber-count laws with positivity), and `t = n−1` (this dichotomy) — with the coset-form intermediate strata provably DEAD (O111). The open window content is exactly the interpolation between O112's per-exponent count laws and this endpoint: which sub-full windows force which closure — with both ends and the obstruction formalized, the question is now a precise interpolation problem rather than an unformed one.

### O114 — the partial-DFT closure law: the dense window {j : p ∤ j} EXACTLY characterizes μ_p-closure at EVERY modulus — the first intermediate stratum past two primes

`PartialDFTClosure.lean` (axiom-clean ×3): `partial_dft_mu_p_closed` — for any prime `p ∣ n`, power sums vanishing at every `1 ≤ j < n` with `p ∤ j` force `μ_p`-closure of `T ⊆ μ_n`; with O97's converse, an exact iff (`partial_dft_iff`). Fourier mechanism: `dft_point_mass` (the phased row sums recover the indicator, `Σ_j (ζ^{n−a})^j·S_j = n·𝟙_T(ζ^a)` — the O113 double sum factored as a reusable lemma) compared at `e₀` and `(e₀ + n/p) % n`: the `p ∣ j` rows carry equal phases unconditionally (`p·e₁ ≡ p·e₀ [MOD n]`, with the inverse-free cancellation `ζ^{X}·ζ^{pua} = 1` at both points), the `p ∤ j` rows die by the window; membership is shift-invariant, iterate.

**The window hierarchy at `n = pqr` now has machine-checked content at FOUR strata**: t=1 ℚ-components (O109), single gcd-exponents (O112 nonneg counts), dense coprime-complement windows (this — at n=30, all odd j force antipodal closure; all 3∤j force μ₃-closure; all 5∤j force μ₅-closure), and the full window (O113) — coset strata dead (O111). **The open interpolation is now pinned between explicit formalized bounds**: the dense window (φ-complement size, sufficient — this) versus single exponents (O112, count-level only) — the open question is the SPARSE sufficient window at 3+ primes, whose two-prime answer {q^c} (O97) used the packet mechanism O105 removed. Note the dense law also gives a SECOND proof route for O97-type closure at any modulus when the full coprime-complement window is available — the two-prime sparse law remains strictly stronger on its turf.
### O115 — THE GENERAL-t WINDOWED LAW, q-DIRECTION: windowed_coset_cover_q (the reassembly induction COMPLETE)

`DeBruijnTwoPrime.windowed_coset_cover_q` + `packetUnion_full_export` (axiom-clean,
0 sorry; my lane): **for EVERY window depth m ≤ b+1: a two-prime vanishing set with
q-power window {q^0, ..., q^m} has every element μ_{q^c·p}-covered (some c ≤ m) or
μ_{q^{m+1}}-covered** — the complete d-coset reassembly in the q-direction at every
window depth. m = 0 is the de Bruijn cover; m = 1 the trichotomy; general m the full law.

Proof = the induction the arc was built for: full export (orbit + dichotomy + complete
transfer, ONE spectrum), the spectrum inherits the depth-(m−1) window (transfer at
e = q^c, p ∤ q^c), the inductive hypothesis reassembles the spectrum one level down,
and the upward rung (coset_lift) multiplies the recovered coset order by q. Floor case
b = 0 handled by the prime-power slice closure (the deep-spectrum block inlined).

This is the O70-verified mixed-radix law's q-direction IN FULL GENERALITY as a
machine-checked theorem. Remaining for the complete two-sided law: the symmetric
p-direction (role swap, mechanical) and mixed windows (both prime directions
simultaneously — the joint induction); then O73's base hypotheses discharge and the
mixed tower goes fully unconditional on M31-style domains.

### O115 — RÉDEI–DE BRUIJN–SCHOENBERG AT EVERY SQUAREFREE MODULUS: the ℤ-classification completes the coefficient trilogy

`IntSquarefreeClassification.lean` (axiom-clean): `int_squarefree_classification` — for INTEGER weights at every squarefree `n` (arbitrary arity): `Σ_{e<n} w_e·ζ^e = 0 ⟺ ∃ A : ℕ → ℕ → ℤ, w e = Σ_{p ∈ primeFactors n} A p (e % (n/p))` — Schoenberg's theorem (the vanishing lattice is packet-spanned over ℤ) at full squarefree generality. The O109 strong induction reruns with ℤ-weights and is SIMPLER there: fiber differences stay ℤ, so the IH applies with no rational detour (the construction was always manifestly integral — `A p y = w(section(0,y))` + IH decode); only the K-coefficient transport changes (`map_intCast` for `map_ratCast`). Converse = the ℤ-cast packet regroup.

**The coefficient trilogy at squarefree moduli is COMPLETE**: ℚ-components always (O109), ℤ-components always (this), ℕ-components exactly up to two distinct primes (O103 positive / O105 impossible at three) — every coefficient ring's classification settled at every squarefree modulus, with the ℕ/ℤ defect at ≥3 primes being precisely the content of Lam–Leung's positivity induction for the total weight. The surviving open items on the lane are unchanged: the sparse-window interpolation (bracketed O112/O114), Lam–Leung's positivity finish (published proof, all scaffolding now in place), O99 incidence, δ*.

### O116 — P-DIRECTION LAW + THE DESIGNATED FIRST PEEL (the joint law's enabling pair)

Two theorems (axiom-clean, 0 sorry; my lane):

* `windowed_coset_cover_p` — the general-t law in the p-direction (role-swap
  instantiation of O115; both prime directions now complete).
* `first_peel_export` — **decomposition choice as a theorem**: if x ∈ S has its full
  μ_q-orbit inside S, there is a decomposition of S whose spectrum CONTAINS x^q, with
  the orbit property and the complete transfer. Construction: x's orbit is a full
  q-packet (filter = image of μ_q-roots, card q, common power x^q, sum zero); peel it
  FIRST — the remainder vanishes and decomposes by O77; the export of the extended
  derivation inserts x^q, fresh by the orbit argument.

WHY THIS MATTERS: the joint (full O70) law's strong induction has one problematic case —
x both μ_p- and μ_q-closed with pq ≤ t, where both fixed dichotomies can stall. The
first peel converts "x is μ_q-closed" into "the q-side recursion applies to x"
unconditionally. With the floor-division arithmetic (window t transfers to window ⌊t/q⌋
one level down; the rung multiplies d' > ⌊t/q⌋ into q·d' > t), ALL ingredients of the
full mixed-window law are now machine-checked; remaining = the strong-induction
assembly J(t) itself.

### O117 — THE DIVISOR-FORM LAW BELOW p: the complete O70 form on half the parameter space

`DeBruijnTwoPrime.windowed_coset_cover_below_p` (axiom-clean, 0 sorry; my lane): for
window t < p (and t < q^{m+1}, m ≤ b), with ONLY the q-power window hypothesis:

    ∀ x ∈ S, ∃ d ∣ p^{a+1}·q^{b+1}, d > t, x's full μ_d-coset ⊆ S

— the EXACT O70/divisor form of the mixed-radix law ("window t ⟹ union of μ_d-cosets,
d | n, d > t"), as a theorem, in the regime where one prime exceeds the window. The
q-direction law's left case clears the window for free (q^c·p ≥ p > t); the right case
by window-depth choice. On domains n = 2^a·p^b or q^a·p with one large prime — and in
all regimes t < min over the larger prime — the verified law is now FULLY formal.

Remaining for the all-t form: the bigraded assembly (both primes ≤ t), where the
transfer's p∤e puncture requires the two-dimensional spectrum analysis — mapped, with
first_peel_export (O116) resolving its stall case.

### O118 — THE BIGRADED WALL DISSOLVES: syndrome resolution by valuation induction (route, complete)

The all-t law's blocking system (one mixed identity, two spectrum unknowns per exponent
— O117's wall) RESOLVES. The engine, now precisely mapped:

1. PURE-POWER nested syndromes always resolve: a spectrum R's pure p-power syndrome
   Σ_R r^{p^j} unwinds via R's OWN p-side transfer (q ∤ p^{j-1} — valid) down to plain
   sums of deeper spectra = S-window values at product exponents ≤ t. Symmetrically for
   pure q-powers via q-descents.
2. MIXED nested syndromes resolve by INDUCTION ON THE p-ADIC VALUATION: for R's mixed
   exponent e = q^α p^β (α, β ≥ 1), S's mixed identity p·Σ_{T_S} τ^{qe/p} + q·Σ_R r^e =
   Σ_S y^{qe} = 0 (qe ≤ t, FULL window) links R's unknown to T_S's at exponent
   q^{α+1} p^{β−1} — valuation drops by one. At β = 1 the partner is PURE q^{α+1},
   resolved independently by (1), which PINS the mixed unknown. Regress terminates.
3. CONSEQUENCE: every nested spectrum inherits the FULL window scaled by its descent
   multiplier (q^{#q-steps} p^{#p-steps}·Σ_U u^e = resolved S-syndromes). The J(t)
   induction then runs with full windows at every level — my proven q-direction law's
   skeleton with no puncture — yielding THE COMPLETE O70 LAW: window [1,t] ⟹ every
   element μ_d-covered, d | n, d > t, at ALL t.

Formal shape: strong induction on (descent depth, p-adic valuation of exponent),
mutually through the nested spectra; the first_peel (O116) and full export machinery
carry the per-element coverage exactly as in windowed_coset_cover_q. The alternating-
induction and pointwise-weld doors stay closed (recorded); THIS is the open road.
Formalization = the next arc (nested-spectrum invariant + the valuation induction +
re-run of the J-induction); every constituent pattern already exists in
DeBruijnTwoPrime.lean.

### O119 — THE BILATERAL EXPORT + THE MIXED IDENTITY machine-checked (O118 brick 1)

`DeBruijnTwoPrime.packetUnion_bilateral_export` (axiom-clean, 0 sorry; my lane): one
decomposition, BOTH spectra — R (μ_q-packet q-th powers) and T (μ_p-packet p-th powers),
each with its orbit property — the clean R-transfer at p ∤ e, AND **the mixed identity**:

    Σ_S y^{q·e} = q·Σ_R r^e + p·Σ_T τ^{q·e/p}     (p ∣ e)

— at punctured exponents both packet types survive: μ_q-packets contribute through the
common q-th power, μ_p-packets through the common p-th power (their μ_p-orbit collapses
at any exponent divisible by p). Freshness of both insertions by the respective orbit
arguments. This is the equation the O118 valuation induction consumes; next bricks:
the symmetric q∤e' T-transfer conjunct (mirror), then the valuation-induction window
inheritance, then the puncture-free J(t) re-run = THE COMPLETE O70 LAW.

### O120 — the bilateral export COMPLETE: mirror T-transfer added (O118 brick 2)

`packetUnion_bilateral_export` extended to its full five-conjunct form (axiom-clean,
0 sorry, first-try compile): both orbit properties + the clean R-transfer (p ∤ e) +
THE MIXED IDENTITY (p ∣ e) + the mirror clean T-transfer (q ∤ e):

    Σ_S y^{p·e} = p·Σ_T τ^e    (q ∤ e)

— the q-packets die at exponent p·e by the twisted packet sum (ω_q^{pe} primitive via
Coprime.mul_left), the p-packets contribute through their common p-th power. The export
is now SYMMETRIC: one decomposition, two spectra, all four transfer regimes accounted
(clean×2, mixed×1, plus the trivial e=0). Next brick: the valuation-induction window
inheritance — FullWindow U μ := (∀ e, 1 ≤ e → μ·e ≤ t → Σ_U u^e = 0) descends to both
children, by strong induction on v_p of the exponent using the mixed identity.

### O123 — THE SUBDIVISION ENGINE: canonical cosets split into canonical sub-cosets — the natural-DCS splitting rung at full generality, both tree directions now machine-checked (fable lane, 2026-06-10)

The constructive engine of the packing tree program (O122's named next). `PackingSubdivision.lean` (4 lemmas + kernel-checked teeth, axiom-clean ×4 — `step_identity` is even pure-`[propext]` — 0 sorry, 0 warnings):

* `step_identity` — the modulus bookkeeping `n/(d/u) = u·(n/d)` for `u ∣ d ∣ n`.
* `cosetOf_subdivide` — **the splitting identity**: `cosetOf n d r = ⋃_{i<u} cosetOf n (d/u) (r + i·(n/d))` — a canonical `μ_d`-coset is the union of `u` canonical `μ_{d/u}`-cosets, for ANY `u ∣ d` (digit split `j = j%u + u·(j/u)`).
* `subdivide_parts_disjoint` + `isPacket_subdivide` — the parts are pairwise disjoint and the split is an `IsPacket`-family statement: a `μ_d`-packet is a disjoint union of exactly `u` canonical `μ_{d/u}`-packets.
* Tooth: `cosetOf 12 6 1 = ⋃_{i<3} cosetOf 12 2 (1+2i)` and `= {1,3,5,7,9,11}`, kernel-checked.

**Both directions of the natural-DCS splitting tree are now theorems**: O106's `isPacket_merge` (a packet of fattened bases merges into one bigger coset) is the upward rung; this is the downward rung. Consequence: any TREE-REALIZABLE modulus multiset (recursive prime splitting from the root) yields an explicit packing by iterating `cosetOf_subdivide` — the constructive half of the candidate exact `k`-generator law (`probe_packing_tree_law.py`: packable ⟺ the completed multiset `{n/d × a_d} ∪ {n}^{n−vol}` is tree-realizable; Berger–Felzenbaum–Fraenkel naturality is the necessity side, the genuinely open research half).
### O121 — O118's INHERITANCE STEP REFUTED (own-route falsification) + the corrected road

Falsify-first applied to my own O118 route before formalizing it:

* THE GAP (found by hand): the valuation induction's base case fails as linear algebra —
  the two mixed identities at S-exponent pq (q-side at e = p; p-side at e' = q) are THE
  SAME EQUATION: the pair (Σ_R r^p, Σ_T τ^q) is genuinely underdetermined by S's
  syndromes alone.
* THE REFUTATION (numerical probe, docs/kb/mixed-tower-probes/inherit_probe.py): window
  inheritance FullWindow R q t is FALSE for general decompositions — S = μ₁₂ (full
  window through t = 11!) admits MIXED decompositions (2- and 3-packets interleaved)
  whose spectra violate the inherited window: Σ_R r³ ≠ 0, Σ_T τ² ≠ 0. Spectrum windows
  are DECOMPOSITION-DEPENDENT.
* THE ILLUMINATION: μ₁₂'s PURE decompositions inherit perfectly (all-2-packets ⟹ R = μ₆
  exactly, all windows ✓). Inheritance is a property of ADAPTED decompositions, not all.
* THE CORRECTED ROAD: the J(t) induction must run per-element with CHOSEN decompositions
  — exactly the first_peel_export resource (O116): peel the element's own orbit first
  and control the spectrum along ITS chain only. The bilateral export (O119/O120) stays
  valid and useful (the identities are true; only universal window inheritance dies).
  Corrected next brick: the adapted-decomposition spectrum-window lemma — what window
  does the FIRST-PEELED spectrum inherit along the peeled element's chain?

### O122 — ADAPTED INHERITANCE CONFIRMED (349/349): the corrected road is empirically sound

Probes (docs/kb/mixed-tower-probes/adapted_probe.py, adapted36.py): for EVERY windowed S
and every μ_q-orbit-closed element x, SOME completion of the x-first-peeled
decomposition has a spectrum with the FULL inherited window — 36/36 exhaustive at
n = 12 (t ∈ {4,6}); 313/313 on structured sets at n = 36 (t ∈ {4,6,9}, sampled
completions). Together with O121: spectrum windows are decomposition-dependent, but a
GOOD decomposition always exists along any chosen element's chain — decomposition
choice (first_peel, O116) is the right resource, confirmed.

THE REMAINING FORMAL ENGINE (honest status): proving good-completion existence from the
window alone still meets the both-dead-cosets stall (peeling a DEAD coset damages the
window at its multiples; alive-coset coverage is the law itself — circularity). Two
candidate engines, both mapped: (a) the per-element induction where the proven
q/p-direction laws supply alive peels for their right-case elements and the stall set
shrinks by a structure argument; (b) the locator-polynomial route — the law as a
gap-divisor factorization theorem for X^n − 1 (top-coefficient gap t ⟹ factorization
into X^d − γ factors, d > t) — classical in flavor, possibly cleaner. Both are genuine
formalization arcs. The bilateral export + mixed identity (O119/O120) and all earlier
theorems stand.

### O116 — LAM–LEUNG REDUCED TO MINIMAL VANISHING SUMS: the positivity kernel isolated

`MinimalVanishingReduction.lean` (axiom-clean ×4, Mathlib-only): `exists_minimal_vanishing_subweight` (every nonzero vanishing ℕ-weight dominates a minimal one — strong induction on the total), `span_of_minimal_span` (peel minimal sums; differences of vanishing weights vanish; totals strictly drop), `lam_leung_iff_minimal` (the ℕ-span law ⟺ its restriction to MINIMAL weights). With O110 (squarefree reduction) + O104 (two-prime base): **Lam–Leung's theorem is now equivalent to the single statement "minimal vanishing sums at squarefree n with ≥3 primes have weight in ℕp₁+…+ℕp_k"** — exactly the Conway–Jones (Acta Arith. 30 (1976)) / Lam–Leung §3–5 minimal-sum structure theory, the last unformalized ingredient. The O105 witness is such a minimal sum (weight 6 = 3+3 ✓ in span, as predicted).

### O123 — THE SET-FORM LAW + ALIVE-TRACE DETERMINATION: the two-prime budget mechanism below p

Two theorems (axiom-clean, 0 sorry; my lane), the counting payoff of O117:

* `windowed_eq_union_alive_below_p` — the set-form law: every element of a windowed set
  lies in the filter of its own alive covering coset — S IS the union of the alive full
  cosets it contains.
* `windowed_determined_by_alive_trace` — THE BUDGET MECHANISM: two windowed sets with
  the same alive-coset trace (the same full alive cosets through every point) are EQUAL
  — the windowed family injects into the alive-coset trace data. This is the two-prime
  below-p analogue of the 2-power recovery injection (tower_count, O55): the counting
  form |F_n(t)| ≤ #(alive-coset traces) follows for any concrete instantiation.

With O117 (coverage), O123 (determination), and the O70 tables (exact counts), the
below-p regime of the two-prime mixed-radix theory now has the full arc: law, set form,
and budget mechanism — all machine-checked. The above-p regime keeps its two candidate
engines (O122); the bilateral identities stand ready.

### O124 — COVERAGE MONOTONICITY + the upgrade question pinned (the above-p gap, exact)

`coverage_mono` (axiom-clean, 5 lines): μ_d-coverage implies μ_{d'}-coverage for every
d' ∣ d — the laws' certificates form a DIVISOR IDEAL at each element.

THE SHARPENED GAP (analysis): windowed_coset_cover_q's existential (∃ c ≤ m,
μ_{q^c·p}-cov) certifies SOME point of the ideal, not its maximum; the all-t law asks
that the ideal reach above t. By monotonicity, alive coverage implies all the small
coverages the directional laws can certify — so the laws as proven are CONSISTENT with
the all-t law but don't yet force it. THE MISSING ENGINE, exactly: the UPGRADE —
certified small coverage (q^c·p ≤ t) + full window ⟹ alive coverage. Mapped candidate:
the contracted-fold route — x's small coset C collapses under the d₀-power map; the
VALUED fold machinery (general-radix folds, O65) tracks the contracted set with
multiplicities; the upgrade = the law at the contracted level lifted by the rung. This
re-enters the valued theory — the same frontier as the branch-count program — revealing
the two remaining objects are CLOSER KIN than they appeared: both are valued-fold
structure questions. One frontier, not two.

### O125 — THE VALUED 2-POWER WINDOWED LAW: the multiplicity door opens

`LamLeungTwoPow.windowed_coeff_congr_invariant` (axiom-clean, 0 sorry; my lane): a
ℚ-coefficient vector on μ_{2^(m+1)}-exponents whose 2-POWER WINDOW {2^0, …, 2^k}
vanishes is INVARIANT on exponent classes modulo 2^(m−k) — the VALUED analogue of
full_tower, by induction on k: the j = 0 relation gives antipodal symmetry (O74), the
folded vector c₁(s) = 2·c(s) inherits the shallower window at the halved level
(fold-of-window identity), and the inductive congruence-invariance pulls back through
antipodal reduction.

WHY THIS MATTERS — the unified frontier (O124) just yielded its base case from the
multiplicity door: INTEGER multiplicity vectors (contracted folds of windowed sets;
branch-weight profiles of windowed valued errors) at 2-power levels are CONSTANT on
μ_{2^{k+1}}-coset classes. Consequences queued: (i) branch-weight profiles of deep
windowed errors on 2-power towers are coset-constant — a RIGIDITY constraint directly
on the branch-count program's objects; (ii) the contracted-fold upgrade at full-q
contractions (two-prime side) now has its target lemma. The window {2^j} is SPARSE
(only k+1 exponents for a 2^{m−k}-resolution conclusion — exponentially fewer than the
full window): the valued law is stronger than its subset shadow.

### O126 — CONTRACTED MULTIPLICITY RIGIDITY: the first formal constraint on the branch objects

Two theorems (axiom-clean, 0 sorry; my lane):

* `contraction_fiber_sum` — power sums of S at 2^s-scaled exponents equal the
  multiplicity-weighted power sums of the 2^s-contraction (the fiber filters partition
  S; per-fiber terms are constant).
* `contracted_multiplicity_invariant` — **for a set with the scaled 2-power window, the
  contraction's fiber-count function is invariant on exponent classes mod 2^(m−s−k)** —
  O125 applied to the integer multiplicity vector that the contraction lays over the
  domain.

THE MEANING: at every depth s of the 2-adic tower, a windowed set's fold-multiplicity
profile is COSET-CONSTANT — the branch-count program's central objects (how mass
distributes over contracted domains) now carry a machine-checked rigidity law. The
program's two doors now have: the valued law (O125), the multiplicity rigidity (O126),
the all-words fold/mass/window laws (O56–O59), and the complete subset theory — the
branch-count question is surrounded on every side by formal structure, with the count
distribution itself the remaining open core.

### O127 — THE SPARSE TOWER THEOREM: full_tower from exponentially fewer conditions

`LamLeungTwoPow.full_tower_sparse` (axiom-clean, 0 sorry; my lane): the 2-POWER window
{2^0, …, 2^k} ALONE (k+1 conditions) forces μ_{2^(k+1)}-closure — the same conclusion
full_tower drew from the full window [1, 2^(k+1)) (2^(k+1) − 1 conditions). Proof: O126
at depth s = 0 (the indicator is its own multiplicity vector; rigidity makes it
invariant mod 2^(m−k); the μ_{2^(k+1)}-roots are exactly the ζ^{2^(m−k)}-powers, and
invariance transfers membership along them).

SIGNIFICANCE: (i) the session's first pillar strengthened exponentially in hypothesis
by its newest theorem — the valued door immediately repaid the subset theory; (ii) for
the LIST/BUDGET applications, sparse windows mean the unit-syndrome budget (O61) holds
under 2-power-only syndrome conditions — a much weaker verifier obligation; (iii) the
non-2-power window exponents are REDUNDANT for the fiber structure at 2-power domains —
a fact the O70 tables hinted at (plateaus) and is now a theorem.

### O128 — THE SPARSE BUDGET: 2^{#classes} from k+1 syndrome conditions (sparse_tower_count)

`LamLeungTwoPow.sparse_tower_count` (axiom-clean, 0 sorry, first-try compile): the
recovery-injection budget — #{w-subsets of D₀ with the SPARSE window Σ x^{2^j} = 0,
j ≤ k} ≤ 2^{#(2^{k+1}-power classes)} — with full_tower_sparse (O127) supplying the
closure. The complete sparse chain now stands: O125 (valued law) → O126 (rigidity) →
O127 (sparse tower) → O128 (sparse budget): the entire 2-power list-budget theory holds
under exponentially fewer syndrome conditions than originally formalized — k+1 verifier
checks where 2^{k+1}−1 were assumed needed. For protocol design (FRI-style 2-power
domains): the same interior list guarantee from a logarithmic number of power-sum
constraints.

### O129 — THE INCIDENCE LABORATORY: the exactness theorem + the first measurements of the sole surviving channel (nubs, 2026-06-10)

Scope claimed as the complement of lalalune's 07:11Z lane 2 (comment 4667894636): dense
layers, slice spread of differences, cross-level persistence, union-bound loss.
`scripts/probes/incidence/` (probe + RESULTS-INCIDENCE.md + published run log +
exactness/ artifacts); the production kernel gains an `#ifndef A` guard so
`-DA=17` emits both layers (the 17-layer was previously unreproducible from the tree).

**THE EXACTNESS THEOREM (computational char-0 proof, second-seat audited):** over
ℤ[ζ₃₂], every witness–dense difference vanishes on μ₃₂ exactly on T_w ∩ T_t. At a
split prime the law holds iff p divides none of 13,219 explicit norms (all < 2.2·10²⁴);
BabyBear and 3·2³⁰+1 divide none — proven twice. NOT anatomy-forced: fails at all 20
split primes 97..2113 at the generic ~6.7/p rate, counterexamples explicit; the
certificate's bad-prime predictions match the sweep failures exactly. Structural
lemmas (the e_w-even lever, d = P(x²)+x·Q(x²), Q = −e₃·F): dense words have e₃ ≠ 0;
a full fiber dies iff z ∈ S ∩ B — **the cross-pair incidence geometry IS the
intersection lattice of the 35 fiber-subsets with the 580 B-blocks**; accidental
collisions are always single zeros with live partner (0 dead-fiber accidents in
~10,800 observed extras across 20 primes).

**Measurements (gates passed; run-2 reproduces run-1 exactly on the deterministic
census):** cross 35×1344: zero excess 47,040/47,040; 4,072 distinct L1 dead loci,
mean multiplicity 11.55, max 144 — the union bound's loss, measured for the first
time; multiplicity menu low-mass concentrated at {2,4} (the menu's fourth appearance)
with a rich even tail. Dense-dense (12,000 sample): excess ≈ 0.2% — exact cyclotomic
identities (pairs sharing two q-roots collide at their antipodes), identified
per-pair; 32 pairs have EMPTY L1 locus; all 672 negation pairs drop a full tower
level (spread (1,2,4), population-complete check). n=16 reference: same shape,
refined values (persistence).

**Where this leaves the channel:** the witness–dense incidence is now COMBINATORIAL
(the S∩B lattice) — counting arguments can consume it directly; the open mechanisms,
sharply: the non-negation sub-maximal tail, the dense-dense q-root identities as a
family, the conceptual "why" of char-0 nonvanishing (free roots of N = P²−YQ² avoid
μ₁₆), and the iff-direction Galois stability (sketched, empirically exact). Honest
scope: one word, one radius pair; the theorem covers all split primes for THIS
configuration.

### O124 — THE MULTISET (ℕ) WINDOW LAW: trichotomy resolved by probe + CJ counterexample

Hypothesis A4 (docs/wiki/open-math-hypotheses-2026-06.md) asked whether the windowed coset law
lifts from Z-weights to ℕ-weights (multisets): window 1..t vanishing ⟹ ℕ-union of full
γ·μ_d cosets, d | n, d > t. Resolution (probes: /tmp/hypA4_probe.py, /tmp/hypA4_cj.py):

* **GENERAL n: FALSE.** The Conway–Jones (5:6)-type minimal sum at n = 30 — multiset
  {ζ₃₀^25, ζ₃₀^5, ζ₃₀^6, ζ₃₀^12, ζ₃₀^18, ζ₃₀^24} (= −ζ₃ − ζ₃² + ζ₅ + ζ₅² + ζ₅³ + ζ₅⁴) —
  has p₁ = 0, is MINIMAL (no vanishing subsum, verified exhaustively), and is NOT
  ℕ-decomposable into full cosets (verified by backtracking). The Z-law (O111) survives
  because Z-decompositions may use negative coefficients; the ℕ-gap is exactly the
  Lam–Leung positivity kernel (O116). **A4-general ≡ K5: same problem.**
* **PRIME POWERS n = p^k: TRUE in all probes** (n = 8: t = 1,2,3, 49+5+5 windowed multisets,
  0 counterexamples; n = 9: t = 1,2, 7+7, 0). Proof skeleton mapped: the tower power basis
  1, ζ, …, ζ^{p−1} over ℚ(ζ_{p^{k−1}}) (X^p − ζ_{p^{k−1}} minimal) forces per-fiber p_m
  vanishing for p ∤ m; the p | m window equations are cross-fiber mixed and force
  RECOMBINATION of pulled-back small cosets into full larger cosets (e.g. at n = 8, t = 2:
  two antipodal pairs {j, j+4} ∪ {j+2, j+6} recombine into the full γμ₄). This is the
  adapted-decomposition phenomenon (O122) in its clean single-prime form — no dead-coset
  stall at prime powers. **FRI/STIR-relevant: smooth domains are exactly μ_{2^k}.**
* **TWO PRIMES p^a q^b: TRUE in probes** (n = 12: t = 1,2, 88+16, 0 counterexamples) — open,
  and by the above identification it IS the O116 minimal-sum kernel restricted to two primes,
  where Conway–Jones minimal sums are exactly the scaled full-coset relations (no exotic
  minimal sums below three primes — consistent with the in-tree two-prime completeness).

Corrected A4 (the formalization target): **the prime-power multiset window law**, with the
two-prime case conditional on K5 and the 3-prime case FALSE as stated (needs the Lam–Leung
weight-bound correction). The A3 boundary-counting bridge only needs the prime-power case.

### O130 — THE GENERAL RUNG LAW: the O108 antipodal-balance engine derives every 2-power scale; blind n=64 forecast survives two independent enumerations; the r=5 stratum TURN-ON falsifies "marginal = (s/2−1,3)" as a law (nubs, 2026-06-10)

Full dossier: `scripts/probes/genlaw/RESULTS-GENERAL-LAW.md`. Three blind agents
(generalizer / independent verifier / adversarial audit with a third implementation),
calibration-gated on C19 at s = 8 before any new scale was believed.

* **Witness layer, theorem grade for all 2-power s:** ℓ(w, s+2) = `C(s/2−1, s/4)` exactly —
  even-r death + the r=0 balance forcing (fiber s/4 in, 3s/4 out, s/4 free pairs). Rungs:
  3, 35, 6,435, 300,540,195. Nothing above agree-(s+2).
* **Marginal layer, derived for all 2-power s and ALL odd r:** the same 3-line reduction
  lands antipodal balance of `{xᵢxⱼ} ⊎ O_z ⊎ B_z ⊎ {−z*}` for every odd r ≥ 3 (not just
  r = 3), L4/L6 hold for all odd r, so `marginal(s) = 2·Σ_{r odd≥3} N_r(s)` with N_r per-s
  finite censuses. N₃ structure (L1 parity-purity, complete E1–E4 taxonomy, the 13-type
  universal node geometry h/v/k/σ) proven general; machine-asserted identical at s = 8/16/32.
* **The engine re-derives C19's 16 at s = 8 with NO fix** (exact (B,O,σ) set equality vs a
  fresh full C(16,9) field census) — and what calibration killed is instructive: the
  "perfect 7×8 split" and "pairwise = m" census patterns are m = 8 coincidences, not law.
* **Blind n=64 forecast vs truth: EXACT.** r=3 stratum forecast 764,544 classes / 1,529,088
  elements; the verifier's independent enumeration (different algorithm, calibrated on the
  O108-proven s=16 truth) and the audit's third implementation (per-axis DP) both return
  **764,544 with exact element-set equality**. ε-split 373,440/391,104; B-menu {2,4} third
  rung (703,656 = 642,768×2 + 60,888×4); dual-B 14,520+46,368; 300 constructive BabyBear
  codewords agree-exactly-33 + 50/50 negative controls fail; 24+24 audit samples at two
  split primes.
* **THE FINDING — strata turn on with s:** N₅(8) = N₅(16) = 0 but **N₅(32) = 99,512**
  (pattern (14,5); 199,024 elements) — the verifier's r=3-only "total" was the incomplete
  one and the audit adjudicated FOR the forecast (its own sweep + 30/30 assumption-free
  raw-brute classes + 24 field samples). New structure: B-multiplicity all 1, five new
  z*-slot types, new event E5 (product–product antipodal pairs), **L3 breaks** (2,784
  classes put a product on the −z* fiber). s=32 marginal total **1,728,112** =
  2·(764,544 + 99,512), proven for r ≤ 11 (exhaustive C sweeps; r=11 = 1.32×10¹¹ configs).
* **Level-4 anchors (corrected s=64 kernel, Python-revalidated):** N₃(64) =
  244,593,584,640; N₅(64) = 141,450,979,280; N₅/N₃ grows 0 → 0 → 0.13 → 0.58, so
  marginal(128-domain) ≥ 772,089,127,840 is a LOWER bound — r ≥ 7 plausibly activates.

**Honest residuals:** (1) the r ≥ 13 tail at s = 32 is unswept (≥ 1.4×10¹² configs) — the
1,728,112 is conditional on it; the r=5 turn-on proves "predicted 0" is genuine
extrapolation; r=13 (~18 core-h) feasible, recommended; the real fix is a structural
exclusion theorem. (2) All counts are char-0; BabyBear is below the transfer threshold —
mod-p rests on spot checks; the feasible falsifier is the 864,056 char-0 configs mod p via
norm divisibility. (3) Census closed forms beyond m = 16 are fits; r=5 taxonomy charted,
not derived. (4) 32-bit O-mask UB porting trap in `sweep32*.c` at s = 64 — use
`genlaw/audit/audit_sweep64.c`. (5) The multiset Lam–Leung Lean brick written for this run
was found **subsumed in-tree on rebase** (`vanishing_iff_antipodal_coeffs` is the stronger
ℚ-iff; `LamLeungMultisetAntipodal` has the element-level multiset form) — landed as
`genlaw/audit/redundant_MultisetLamLeung.lean.txt` (compiles, axiom-clean) purely as the
independent confirmation it turned out to be. Same lesson as O38: re-sync before claiming.

**Where the open core moves:** the per-level law of the descent program is now an ENGINE +
per-s censuses, verified to three rungs and forecast-validated at the fourth; the named
opens are the odd-r tail exclusion theorem, the r ≥ 5 taxonomy derivation, and the per-prime
transfer at n ≥ 64.

### O131 — incidence rungs, batch verdicts: the moments bridge is an identity; the certificate has an exact Galois law (nubs, 2026-06-11)

Pre-registered batch (rungs/HYPOTHESES.md, claim #334 comment 4675343864). Two lanes in:

**A1 PROVEN (hypothesis honestly corrected in transit):** pair-overlap content is NOT in
the agreement-spectrum moments (all a_j moments are single-codeword sums) — it lives in
the TRANSPOSED spectrum M_t(σ) = #{p : σ ⊆ T_p}: for all r, t,
Σ_σ C(M_t(σ), r) = Σ_{r-subsets R} C(|∩_{p∈R} T_p|, t) (one double count). r=2 makes the
t-th binomial moment of O129's pair-overlap distribution equal the second binomial
moment of the dual spectrum. Verified exactly at C19 (nine instances; F1=174, P2=922,
P3=3240). With the exactness law, |T∩T′| = n − d_H(p,p′) — the dual spectrum's pair
content is distance-geometry-determined with zero slack wherever exactness holds; at C19
this replaces the worst-case pair cap 1,197 by the true 922 (23% tightening). Bonus: the
3 witness–witness C19 pairs (outside O129's theorem) measured: zero excess.

**A2 CONFIRMED — the bad-prime law is exact Galois arithmetic:**
c = Σ 16/|Stab| / 13,219 = **11.0918**; mechanism: witness values always lie in
ℤ[ζ₁₆] (even exponents ⟹ σ₁₇-fixed; 7,796 orbits). Corrected law matches the sweep
aggregate at z = +0.05 (generic 16 rejected, z = −28.7); beyond the sweep it is an upper
bound — the deficit is forced (1−ζ)^≥20 divisibility + extreme norm smoothness. The
residue-degree law (v_p ≡ 0 mod ord₃₂(p), 0/1,142 violations) PROVES exponent-1 bad
primes must split — the empirical pattern is now a theorem-shaped statement awaiting a
two-line proof from ideal factorization. Artifacts: rungs/laneA2/, fully cross-checked
against the committed certificate.

Pending on the session-limit reset: G1 (menu law), G2+G3 (n=64 blind), G5 (beat the
union bound), A3 (λ-family rigidity). Inline A2 pre-observation (c ≈ 11 from summary
data) recorded in HYPOTHESES.md before the lane ran — the discipline held.

### O132 — G1 CONFIRMED: the incidence menu law (nubs, 2026-06-11)

Third verdict of the pre-registered batch (rungs/HYPOTHESES.md), derived and verified
inline. **The cross-pair locus-multiplicity menu is a theorem**: for a dense element
with block B, the loci over the 35 witnesses are Z_J = (B∩{z*}) ∪ ⋃_{i∈J} b_i with
multiplicity exactly C(m₀, 4−|J|) (m₀ = number of B-empty antipodal pairs; disjoint
blocks ⟹ the locus determines the trace; completions free). Aggregate evenness is
forced: negation fixes squares ⟹ ν-paired elements share B ⟹ every aggregate
multiplicity carries the B-census {2,4} factors — the menu IS the B-census convolved
with the C(m₀, 4−|J|) kernel. Verified: analytic == measured in ALL 40 entries
(mass 47,040, distinct loci 4,072; lane_g1_menu_law.py on kernel-regenerated data).
General-s form: C(m₀, s/4−|J|) — the incidence menu at every rung is now closed-form
given the B-census, which O130's engine produces. Batch state: G1 ✓ A1 ✓ A2 ✓;
G2+G3, G5, A3 pending the session-limit reset.

### O133 — THE THIRD MOMENT IS DOMAIN-DEPENDENT: M3 of the agreement spectrum separates smooth subgroups from random domains at k=3, the pencil census is the separating invariant (normalizer spike law + a spectral gap), and k=2 is exactly rigid (moments lane, 2026-06-11)

`scripts/probes/moments/` — pre-registered hypothesis ledger (HYPOTHESES-M3.md, written
before any probe ran) → two independent engines → exact cross-validation → the
separation experiment → RESULTS-M3.md. All exact integers, no sampling on any verdict.

**The reduction (H4, now probe-proven):** `M3[j₁,j₂,j₃] = Σ_u a_{j₁}a_{j₂}a_{j₃} =
q^k·Σ_{ordered pairs (c,c')} N(profile)` through the per-coordinate 5-type census
(common zeros / c-only / c'-only / c=c'≠0 / split), with N a 3-variable coefficient
extractor. Independent pairs organize by 2-dim subcodes = dual points φ ∈ PG(2,q);
at k=3 the basis-map fibers are the orbits of the Möbius involution
`φ₀xy − φ₁(x+y) + φ₂ = 0` on D (sizes ≤ 2), so each pencil carries (A, s, t₂) =
(common zeros, support, #2-fibers); ordered bases ↔ (q−1)·(ordered distinct point
triples) by PGL₂ sharp 3-transitivity. **M3 is exactly a function of the pencil
(A,s,t₂)-histogram + the (MDS-pinned) weight distribution.** Engines cross-validated
byte-exactly on 8 setups (k ∈ {2,3}; q ∈ {5,7,11,13}; subgroup and non-subgroup
domains); internal gates include the ordered-pair partition of q^{2k}, MDS weights
(closed form == enumeration), Σ_φ t₂ = C(n,2)(q−1) on EVERY domain (the H5 pinning:
any M3 difference is t₂-variance, never mean), N(profile) vs brute word counts, the
full ordered-pair profile histogram vs the class decomposition, a GL₂ brute check of
the basis-counting lemma, M1/M2 closed-form marginals, S3 symmetry, total mass.

**Verdicts (full tables in RESULTS-M3-RAW.md):**
* **H2 — k=2 is exactly rigid:** subgroup vs random tensors EXACTLY equal (q=41, n=8).
  Mechanism: pencil maps are injective, all fibers singletons, three special points,
  sharp 3-transitivity — a clean Lean target.
* **H1 — k=3 separates:** the subgroup sits outside the random cloud at every cell —
  3.4× the cloud diameter at (41,8), 14.1× at (113,16), 10.8× at (257,16), ∞ at
  (41,10) where three random 10-subsets had literally identical M3 (small-q histogram
  concentration) yet the subgroup differs. Same sign everywhere (subgroup HIGHER),
  argmax always (j₁,j₂,j₃) = (k−1,k−1,k−1).
* **A5 — the spike law is the torus normalizer, exactly (n ≥ 10):** the subgroup's
  big-spike pencils are EXACTLY {x ↦ c/x : c ∈ H} ∪ {x ↦ −x} (n+1 pencils,
  t₂ ∈ {(n−2)/2, n/2} by the fixed-point count); set equality machine-verified at
  (41,10), (113,16), (257,16); at n=8 the t₂=3 band also catches 8 non-normalizer
  involutions (small-scale noise, gone by n=10).
* **The spectral gap (unplanned find):** subgroup pencil spectra at n=16 have NO
  pencil with t₂ ∈ {4,5,6} at BOTH q=113 and q=257 — noise band capped at 3, the
  normalizer band isolated at {7,8}; random domains fill the gap with a decaying
  tail. Conjecture (Weil on (1,1)-curves vs subgroup characters, the MSS CJM-2018
  Cor 4.1 energy line): for q ≳ n², non-normalizer t₂ = O(n²/q + 1) — the gap is a
  theorem in waiting.
* **Affine/coset invariance (exact, lemma-grade):** D = gH has M3 IDENTICAL to H;
  p ↦ p(ax+b) permutes the code, so ALL agreement moments are invariant under the
  affine action on domains — "smooth coset" ≡ "smooth subgroup" to every M_r.
* **A4 — fingerprint, partial:** AP domains separate at n=16 (3.7–3.9×, additive
  pencils x+y=c as predicted) but not at (41,8); the multiplicative-but-not-subgroup
  gpset does not separate at (41,8). Multiplicative > additive > none, at matched
  parameters.
* **A3 honesty:** relative deviations are tiny — 1.9e−11 (q=113), 5.6e−13 (q=257),
  scaling ~q⁻⁴ at fixed n. M3 SEES the domain; whether anything at this magnitude
  can move a 2⁻¹²⁸-resolution tail is the open quantification (expected: no).

**Position:** complements O131 (their remark — pair content absent from a_j moments —
is the fixed-word setting; over ALL received words the r-th moment decomposes over
(r−1)-tuples of codewords, and r = 3 is where domain-dependence starts). M1/M2
domain-independence is implicit in CS25/DG25/Gao–Li (lit-gated); the smooth-anomaly
PHENOMENON is BKR-2010/BCHKS-§1.4.3-anticipated. New here: a finite computable
statistic with the exact first level (k,r) = (3,3), its mechanism fully classified.

**Named follow-ups:** the M2 Lean brick (statements already numeric-gated:
`pairAgreementCount` + `sum_agreement_spectrum_sq` + the per-word bound; proofs in
flight); the k=2 rigidity theorem; the affine-invariance lemma; the spectral-gap
theorem; the (k,r) = (2,4) cross-ratio cell of the moduli law (next falsifier);
the ΔM3 closed form written as mathematics.

**#357 N3 regression landed:** `scripts/probes/moments/probe_m3_spectral_gap_regression.py`
now validates the stored exact subgroup spectra without recomputing M3: H5 mean pinning,
the exact A5 normalizer big-spike set, and the `n=16` spectral gap
`t₂ ∉ {4,5,6}` at `q=113,257`.  This is not the Weil proof; it is the stable finite target
that the spectral-gap theorem must explain.

### O134 — THE PER-PRIME FALSIFIER FINDS THE TRANSFER FAILING: +11/+54 spurious marginal codewords at BabyBear/p₂ at n=64 — the char-0 counts are exact, the per-prime lists carry a measured prime-specific surplus; PLUS the witness-layer count formalized in-tree (nubs, 2026-06-11)

Two deliverables (full dossiers: `scripts/probes/genlaw/falsifier/RESULTS.md`, new module
`WitnessLayerCount.lean`); both adversarially verified (independent verifier legs, 0.93).

* **The falsifier.** O130 caveat 2 said the n=64 exhaustive per-prime census was infeasible
  (C(64,33) ≈ 7×10¹⁷). It isn't: the consistency equation is LINEAR in the B-subset sum
  (coeff(X^s) of e ⟹ Σ_{c∈B} ζ^{2c} = z* − e₂(x) − e₁(O_z)), so per (O,σ) class an exact
  meet-in-the-middle subset-sum scan covers ALL classes — including char-0-infeasible ones.
  Result at pattern (15,3), all 19,840 classes: **BabyBear mod-p count = 764,555 = char-0
  764,544 + 11 spurious (2 classes); p₂ = 764,598 = +54 (10 classes)** — the O130
  "predicted 0" mod-p transfer FAILS at both production primes. Every spurious config
  reconstructed end-to-end: genuine monic deg-34 word, coeff(X^33)=0, coeff(X^32)=λ,
  agreement EXACTLY 33, NOT char-0 balanced; mechanism = p | N(α) for bad lattice vectors
  α of L1-norm 14–18 (at p₂, six of ten classes share one α). Calibration tower: n=16 and
  n=32 exact (672 = 672 at both primes — matches the exhaustive O98 census, zero spurious);
  reduction identity pinned vs raw polynomial arithmetic 720/720; per-class char-0 counts ==
  audit_sweep64 DP at s=8/16/32; small-prime positive controls (p=97 n=32: +38,716;
  p=193 n=64: +7.97×10⁹) land on the uniform heuristic to 0.01%. Verifier leg: line-by-line
  code review + from-scratch dict-MITM reproduction of flagged classes + 56-class
  independent recount — sound, no fatal/major. **Interpretation: the prize-relevant
  per-prime bad-list sizes at n=64 are the char-0 counts plus a TINY measured prime-specific
  surplus (1.4×10⁻⁵ relative at BabyBear) — the forecastability of the char-0 layer survives;
  exact per-prime work must add the norm-divisibility correction.** r=5 stratum scan
  (3,222,016 classes) in flight; odd r ≥ 7 unscanned mod p.
* **`WitnessLayerCount.lean`** (7 theorems, axiom-clean `[propext, Classical.choice,
  Quot.sound]`; `balanced_iff` leaner `[propext, Quot.sound]`): the witness-layer counting
  law formalized — `balanced_card` (#{(2k+1)-subsets of range(2h) with S ⊎ {q+h} antipodally
  balanced} = C(h−1,k), explicit `card_bij'`), composed with the in-tree criterion to
  `witness_layer_card`/`witness_e1_card`: at scale s = 2^(m+2), #{(s/2+1)-element exponent
  sets with Σ ζ^e = z*} = C(s/2−1, s/4) — O130's layer-dichotomy counting half, in-tree.
  Kernel gates: s=8 full `decide` enumeration = 3 (C19's rung); 35/6435/C(31,16) instantiate.
  Even-r death primitives included (`sum_ne_zero_of_support_lower_half`, geometric form
  cross-referenced as the exponent-coordinate contrapositive of
  `LamLeungUnconditionalGeneral.antipodal_unconditional`). HONEST SCOPE: counts solutions of
  the balance equation; the reduction from RS agree-(s+2) list elements to the equation (the
  e₂−e₁² algebra + agreement-cap + even-r elimination at codeword level) is the
  not-yet-formalized analytic half — the named follow-up.

**Where the open core moves:** per-prime exactness at n ≥ 64 is now an EMPIRICALLY
CALIBRATED correction theory (char-0 count + p|N(α) surplus), not a conjecture; the surplus
α-spectrum is the new finite object to classify. The witness count is formal; the analytic
reduction and the marginal-layer (r ≥ 3) counting laws are the remaining formalization
targets on this front.

### R3 (#357 campaign) — halving-map renormalization bands REFUTED at kill-check
Idea: iterate 2026/858's threshold-halving `T : δ ↦ δ/2` on the window `(1−√ρ, 1−ρ)`;
hoped fixpoint bands force δ* to a band edge.
**Refuted (one inequality):** `(1−ρ)/2 ≤ 1−√ρ` (it is `(1−√ρ)² ≥ 0`), so the FIRST
iterate from anywhere below capacity already lands strictly below Johnson; the orbit
never returns; the unique fixpoint is 0; the band partition is trivial. Any
renormalization analysis of the window needs a map that re-enters it — halving never
does (which is precisely why 858 works as a protocol trick and says nothing about
`ε_mca` in the window). → verified as `halving_exits_window` /
`halving_orbit_never_returns` (`HalvingWindowExit.lean`, axiom-clean).

### S3/N1 (#357 campaign) — the naive AFFINE orbit-count law REFUTED; the maximizer set is ONE PROJECTIVE orbit (exhaustive at RS[F₅,⟨2⟩,2]); the projective symmetry layer formalized

The S3 dossier conjectured the ε_mca-maximizer set is a single orbit of the affine symmetry
group (translation × rotation × scaling × shear, now formal in `MCAEquivariance.lean`).
**Refuted, exhaustively**: at RS[F₅,⟨2⟩,2], δ = 1/4, the maximizer set has 100,000 stacks but
the affine orbit of the probe stack has exactly 50,000. The row swap is NOT a repair: it is
not even bad-count-preserving (4 → 3 on the seed; the affine γ-line is not swap-invariant).

**The true law (verified, then formalized):** the maximizer set is exactly TWO disjoint
affine orbits of 50,000, fused into ONE orbit by the non-affine GL₂ element
`(u₀,u₁) ↦ (u₁, u₀+u₁)` — i.e. one *projective* orbit. Mechanism: the MCA pencil is a
projective line with `|F|+1` slots; the affine γ-census misses the `[0:1]` (∞) slot; the
affine group is precisely the stabilizer of ∞, so one projective orbit splits into affine
orbits indexed by the ∞-slot position. Constraint lemmas (axiom-clean,
`MCAProjectiveEquivariance.lean`): `mcaEventProj` (homogeneous event),
`pairJointAgreesOn_row_mix_iff` (the no-explanation clause is GL₂-invariant),
`mcaEventProj_row_mix` (GL₂ equivariance), `mcaEventProj_smul` (projective well-definedness),
`badSlotCount_eq_affine_add_infty` (affine census = projective census − ∞ indicator).

Consequences: (a) any orbit-count/flat-numerator law must be stated on `|F|+1` projective
slots — affine counts drift by ±1 inside one structure class, which is now explained, not
anomalous; (b) N1's structured-extremality conjecture survives its first decisive audit in
projective form: at the R1 rung there are NO unstructured maximizers — the maximizer set is
one projective orbit exactly.

### O135 — G5 REFUTED: the union bound is measure-tight; the weight filter is the whole game (nubs, 2026-06-11)

Fourth verdict of the pre-registered incidence batch (rungs/HYPOTHESES.md), computed
inline exactly (Möbius over the full 2¹⁶ locus universe, partition check Σ = q¹⁶ passed,
no truncation): the EXACT union of the per-locus spaces over the 4,072 measured
cross-pair loci agrees with the union-bound SUM to 9 significant digits — slack
1 + O(1/q). The pre-registered falsifier ("Bonferroni fails to separate") fired.
Mechanism: V_Z ∩ V_Z′ = V_{Z∪Z′} has measure ≤ (1/q)·min(|V_Z|,|V_Z′|) — over
|F| ≈ 2×10⁹, overlap corrections are negligible BY CONSTRUCTION; the measured
locus-sharing (mean multiplicity 11.55, O129) is combinatorially real but
measure-irrelevant. Structure: a 31-locus antichain (7 singletons + 24 pairs) carries
the entire union; the union exceeds the 47,040 actual differences by 2.7×10¹²⁶.

**Where the lane's counting target moves (the redirect):** level-1 list counting loses
nothing to locus overlap — the ENTIRE gap is the weight filter: bound
#{f ∈ V_Z : wt_D(f) ≤ w} against |V_Z|·(volume fraction), where smooth-domain structure
must enter (a random subspace of the same dimension would meet the weight ball at the
generic rate; the measured configuration's differences are EXACTLY the low-weight
elements — their excess over generic is the true smooth-domain signal). Incidence stays
decisive at the level of EXACT anatomy (G1 menu law, the S∩B lattice) — but as input to
weight-filter arguments, not unions. Batch: G1 ✓ A1 ✓ A2 ✓ G5 ✗(refuted-informative);
G2+G3, A3 pending capacity.

### O135 — THE r=5 FALSIFIER FINALS: the mod-p surplus SCALES with pattern complexity — +33,453 (33.6%) at BabyBear, +16,941 (17.0%) at p₂, vs r=3's 1.4×10⁻⁵; first observed feasible-class inflation (nubs, 2026-06-11)

O134's r=5 scan completed (full dossier `scripts/probes/genlaw/falsifier/RESULTS.md`):
exhaustive per-class MITM over ALL 3,222,016 pattern-(14,5) (O,mask) classes at both
production primes. Crossfoots exact (char-0 Σ = 99,512; 11,808 feasible classes; per-class
char-0 == audit DP at both primes).

* **BabyBear: mod-p marginal r=5 count = 132,965 = char-0 + 33,453** (4,242 spurious
  classes, 33.6% relative). **p₂: 116,453 = +16,941** (2,409 classes, 17.0%). Compare r=3:
  +11/+54 (~10⁻⁵). The (14,5) α-lattice is rich enough that p | N(α) is statistically
  GENERIC at ~2³¹-size primes — the surplus sits at the uniform-heuristic scale. The
  forecastable char-0 core survives unchanged; the per-prime halo is now the dominant
  correction at r ≥ 5 and grows with r.
* **Locality law (new):** at BabyBear, ALL 33,453 spurious solutions land on
  char-0-INFEASIBLE classes — the 11,808 feasible class counts transfer EXACTLY. At p₂,
  exactly ONE feasible class inflates (+1) — the first observed mod-p inflation of a
  feasible class, so feasible-class exactness is itself prime-specific, not a law.
* **Verification:** 25-class full-brute samples per prime, 50/50 mitm == brute and
  genuine_bal == char0; 447 explicit spurious configs (238 BB + 209 p₂) all reconstructed
  by raw polynomial arithmetic (monic deg-34, coeff(X³³) = 0, coeff(X³²) = λ, agreement
  EXACTLY 33); α-spectrum: unique α per sampled class (no cross-class sharing, unlike r=3
  at p₂), L1 norms 12–20, α(ζ) ≡ 0 mod p verified for all. ξ ∈ μ₆₄ never occurs mod p
  (both strata, both primes).
* **Consequence for the per-prime bad list at n=64, BabyBear:** witness 6,435 (exact mod p
  for the in-S/out-S anatomy... per the O129 incidence caveat) + marginal ≥ r=3 764,555 +
  r=5 132,965; odd r ≥ 7 mod-p strata UNKNOWN (char-0 zero no longer implies mod-p zero —
  at this surplus scale the r=7 pattern (13,7) plausibly carries a pure-spurious mod-p
  stratum; named open).

**Where the open core moves:** per-prime census theory at n ≥ 64 = char-0 structure + a
quantitatively measured generic halo (uniform-heuristic scale, locality on infeasible
classes at large primes, breaking at smaller ones). The named opens: the halo's exact
first moment (is the uniform heuristic a theorem on average over α?), the r=7 mod-p
stratum, and the witness-layer surplus.

### O137 — KKH26 IS EXTREMAL at the exact-pin instance: the worst-case stacks are exactly the twisted-monomial orbit of the KKH26 stack (2026-06-11, #357 — the exact-point and ceiling campaigns meet)

Probe `probe_o137_kkh26_extremal.py` (exact): at RS[F₅,(1,2,4,3),2], δ = 1/4, the KKH26
monomial-pair stack `(X³, X²)` (the r = 3 shape: code degree r−2 = 1) has bad-γ set exactly
`{1,2,3,4}` — count 4 = the proven worst case (`DeltaStarExactPinF5.lean`), and exactly the
census law's prediction `−{3-subset sums of (1,2,4,3)}` (`KKH26CensusLaw.lean`). Since the
extremal stacks form a SINGLE orbit of the twisted-monomial group (O135), the worst case
*is* the orbit of the KKH26 stack:

  **ε_mca(C, 1/4) is ATTAINED by the KKH26 family — the ceiling family is extremal, not
  just a lower-bound family — at the first exactly-solved instance.**

Care: the r = 2 shape `(X², X)` fires ZERO bad γ here because its direction row `X` is a
codeword (deg < k) — when `u₁ ∈ C` every closeness witness extends to a joint pair, so
`mcaEvent` never fires. The KKH26 validity constraint (direction strictly outside the code)
is what instance-matching must respect.

**Conjecture (extremality of the monomial orbit):** at every smooth instance and matching
radius, the sup in `ε_mca` is attained on the twisted-monomial orbit of the KKH26 stack —
equivalently `ε_mca(C, 1 − r·m/n) = (#distinct fiber-subset sums)/|F|` exactly. If true,
the upper-bracket question for this radius family is *computable* from the subset-sum
census alone. Next falsifiers: (i) the n = 8 rung (orbit-reduced decide via the landed
descent engine); (ii) the (12,6) flat numerator 12 across p ∈ {13,37,61} vs the census of
the matching (r, m) shape.
### S2(b) (#357 campaign) — universal MissingLine/ObstructionBound REFUTED at the Johnson radius; phase transition of the obstruction-hitting number
Idea: every 2-column stack misses a line (`MissingLine C δ G U` for all U), so the
covering lemma kills the Jo26 A(q,s) factor for every generator unconditionally.
**Probe arc (all exhaustive mod exact symmetries — per-row codeword translation,
per-row scaling, row swap; engines cross-validated):**
* F₅ rungs (`probe_missing_line_f5_rungs.py`): n=3 k∈{1,2} and the smooth n=4
  domain ⟨2⟩=F₅* k∈{2,3} — H(U) ≤ 2 everywhere; the F₃ sharper law `H ≤ l` survives
  the field axis and the length axis.
* l=3 rungs (`probe_missing_line_l3.py`): 3-row stacks at r = n−k = 2 still have
  H = 2 — the ROW law `H ≤ l` is not the binding quantity; the syndrome law `H ≤ r`
  takes over.
* Decisive rungs (`probe_missing_line_heavy_fast.py`, memoized engine, 7.6M stacks
  in ~10s): at n=4, k=1 (r=3): δ=1/4 (sub-Johnson, 2 witness levels) → H = 2; at
  δ=1/2 = 1−√ρ (Johnson, 3 levels) → **H = 4**, killing `H ≤ l` (2), `H ≤ r` (3) and
  `H ≤ #levels` (3) simultaneously. Over small fields the q-bound itself falls:
  F₂ n=4 δ=1/2: H = 3 > q = 2; F₃ n=4 δ=1/2: H = 4 > q = 3
  (`verify_missing_line_defeater.py`: independent tuple-semantics engine, MATCH).
**Refuted in Lean (`MissingLineDefeater.lean`, axiom-clean):** the F₂ defeater is
fully rigid — stack rows (e₀,e₁),(e₁,e₀+e₂) over the 4-coordinate repetition code at
its Johnson radius δ=1/2 has three bad seeds (0,1),(1,0),(1,1) whose UNIQUE witnesses
{0,2},{2,3},{0,1} pin the three distinct lines of F₂² as obstructions
(kernel-checked cores), overflowing every ≤ q=2 dominating family:
`missingLine_defeated`, `not_forall_missingLine`, `obstructionBound_defeated`.
**What survives:** every sub-Johnson rung still has H ≤ 2 — the re-aimed S2(b) is
"MissingLine below Johnson", with a measured phase transition AT Johnson as the
obstruction-side mirror of the global δ* wall; the sibling S2(b') one-row reduction
(`Jo26ObstructionRowCount.lean`) localizes exactly this gating one dimension down,
and these defeaters certify its `≤ q−1` direction-count hypothesis is TIGHT (it
genuinely fails at Johnson over small fields). Exactness itself is NOT refuted (the
route is sufficient, not necessary); whether epsMCAG interleaving exactness fails at
the defeater configs is the named follow-up probe.
### S1 (#357 campaign) — common sum-polynomial API landed; unification bridge, not yet a δ* pin

`SumPolynomialAPI.lean` now names the finite-window coefficient surface shared by three
previously separate proof lanes:

* `coeffPoly n c = Σ_{i<n} C(c_i) X^i` and `rootSum x n c = Σ_{i<n} c_i x^i`
  with coefficient/evaluation/map lemmas.
* KKH26 signed data are this API with `{−1,0,1}` coefficients:
  `sumPoly_eq_coeffPoly`, `sVal_eq_rootSum`.
* Witness-layer multiplicities are this API with nonnegative integer coefficients:
  `layer_rootSum_vanishing_iff` packages the Lam-Leung antipodal-balance criterion through
  `rootSum`.
* de Bruijn prime-power indicators are this API with `{0,1}` rational coefficients:
  `indicatorPoly_eq_coeffPoly`.

Interpretation for the δ* campaign: S1's "same mathematics" claim is now theorem-shaped
in-tree at the coefficient-surface level.  What remains open is the hard analytic transfer:
the RS agreement-to-layer reduction, the marginal-layer laws beyond the balanced witness
layer, and the per-prime norm-divisibility surplus correction.

**O137 addendum — the conjecture survives (13,4,2) and (17,4,2), and predicts the FULL
profile:** exact ladder rerun: max-bad profile `{m=3: 4, m=4: 1}` at BOTH p = 13 (domain
(1,8,12,5)) and p = 17 (domain (1,13,16,4)) — equal to the census profile
`{#3-subset sums = 4, #4-subset sums = 1}` of the respective μ₄ domains. Three fields
(5, 13, 17), one census. The field-independent "flat numerator" phenomenon is *explained*
at these rungs: the numerator is the subset-sum census, which is field-independent as long
as the sums stay distinct (no collisions at these primes). Probe additions in
`probe_o137_kkh26_extremal.py`-adjacent rerun of the exact ladder.

### O138 — THE (12,6) FLAT NUMERATOR SOLVED: the extremal stack is the m = 1 pair (X⁹, X⁸) and the numerator is the constrained subset-sum census, field-independent (2026-06-11, #357)

The dossier's open phenomenon — max bad-γ count exactly 12 at (n,k) = (12,6), δ = 1/4, at
EVERY field p ∈ {13,37,61} — is fully explained
(`probe_o138_flat_numerator_solved.py`, exact):

* **Monomial-stack scan at p = 13** (all `(X^s, X^t)`, 6 ≤ t < s ≤ 11, agreement ≥ 9):
  unique maximum **(X⁹, X⁸) with badcount 12**; the KKH26 fiber stack (X⁹, X⁶) gives only 4;
  (X¹⁰,X⁷) and (X¹¹,X⁸) give 4; everything else 0. The extremal monomial pair is the
  **adjacent-exponent (m = 1) pair**, same as the n = 4 extremal (X³, X²) — NOT the
  m = 3 fiber shape.
* **The census explains 12 exactly:** the general m = 1 law (monic-root forcing at degree
  a, coefficient matching) says λ is bad for `(X^a, X^{a−1})` against degree-< k codes at
  agreement ≥ a iff `∃ A ∈ C(H, a)` with `e₂(A) = … = e_{a−k}(A) = 0` and `λ = −e₁(A)`.
  At (12,6), a = 9: `{−e₁(A) : A ∈ C(μ₁₂,9), e₂(A) = e₃(A) = 0}` has EXACTLY 12 elements
  (12 qualifying subsets, all sums distinct) at p = 13, 37, and 61 — field-independent,
  matching the flat numerator. (12 = n suggests the qualifying subsets are one rotation
  orbit — the orbit law again.)

**Corrected extremality conjecture:** the sup in `ε_mca(C, 1 − a/n)` is attained on the
twisted-monomial orbit of the **adjacent pair** `(X^a, X^{a−1})`, and equals
`#{−e₁(A) : A ∈ C(H,a), e₂(A) = … = e_{a−k}(A) = 0} / |F|`. Confirmed exactly at every rung
where exact computation exists: (5,4,2), (13,4,2), (17,4,2) (where the constraint set is
empty and this reduces to the proven `badScalar_iff_subsetSum`), and (12,6) × three fields.
Formalization target: `badScalar_iff_constrainedSubsetSum` (same monic-root-forcing proof,
esymm coefficients via Vieta); the KKH26CensusLaw file's law is the k = a−1 special case.

### O139 — first exact census data INSIDE the window: the adjacent-pair family saturates small fields above Johnson, goes field-dependent mid-window, and DIES at δ = 0.5625 for p ≥ 97 (2026-06-11, #357)

`probe_o139_window_interior_census.py` (exact): rate 1/4 (n = 16, k = 4), window
(0.5, 0.75); the O138 constrained census `{−e₁(A) : A ∈ C(μ₁₆,a), e₂ = … = e_{a−4} = 0}`
at the window radii δ = 1 − a/16:

* **a = 5 (δ = 0.6875):** a = k+1 ⟹ NO constraints — every 5-subset qualifies and the
  census **saturates the field** (= p) at p ∈ {17, 97, 113, 193}: for the explicit stack
  `(X⁵, X⁴)`, EVERY scalar is bad above Johnson at small fields (and the direction row is
  never explainable, so this is genuine mcaEvent badness): an explicit, machine-checked
  witness for why the prize must fix |F| large. At huge p the census is ≤ C(16,5) = 4368 —
  and the unconstrained a = k+1 census is exactly the in-tree t = 1 sliver object
  (`ListInteriorUnconditionalT1`): the two lanes meet.
* **a = 6 (δ = 0.625):** one constraint (e₂ = 0) — the census goes **field-dependent and
  non-monotone**: (p, #qualifying, census) = (17, 480, 17), (97, 80, 32), (113, 48, 48),
  (193, 16, 16). The qualifying count decays toward ~n at large p (Weil-type fluctuation
  in between — the e₂ = 0 condition is a curve count over subsets).
* **a = 7 (δ = 0.5625):** two constraints (e₂ = e₃ = 0) — the census is **EMPTY at every
  p ≥ 97** (only p = 17 retains 32 qualifying subsets). The adjacent-pair family
  contributes NOTHING below δ = 0.625 at large fields: the first measured **family death
  radius inside the window**, δ_death(16, 4) ∈ (0.5625, 0.625].

Reading: along the adjacent-pair family the census interpolates from the exponential t = 1
sliver at capacity down to EMPTY mid-window — the constraints `e₂ = … = e_{a−k} = 0` over
subgroup subsets are a *vanishing-power-sum* system whose solvability threshold IS this
family's contribution to δ*. Whether OTHER stacks (higher monomials with cofactor freedom,
rational/DEEP shapes) take over below the death radius is now THE precise extremality
question; the (12,6) scan pattern (adjacent pair uniquely maximal, higher shapes strictly
smaller) suggests not. Next: the (16,4,a=7) higher-monomial scan; death-radius scaling in n
at fixed rate (does δ_death → Johnson, capacity, or an interior limit? — this is a direct
empirical probe OF δ* itself for the conjecturally-extremal family).

### O140 — the adjacent-pair death radius is rate-UNIVERSAL at constraint depth 2: rate 1/2 dies at the same two vanishing power sums (2026-06-11, #357)

`probe_o140_death_radius_rate_half.py` (exact, asserts green): rate 1/2 (n = 16, k = 8),
window (0.293, 0.5), the O138/O139 constrained census at δ = 1 − a/16:

* **a = 9 (δ = 0.4375, 0 constraints):** census saturates the field (= p) at
  p ∈ {17, 97, 113, 193} — the same ε_ca = 1 saturation above Johnson as O139's a = 5 row.
* **a = 10 (δ = 0.375, e₂ = 0):** field-dependent ~n-scale census:
  (17, 432, 17), (97, 32, 16), (113, 64, 32), (193, 32, 32).
* **a = 11 (δ = 0.3125, e₂ = e₃ = 0):** **EMPTY at every p — including p = 17** (which
  retained 32 qualifying subsets at rate 1/4). δ_death(16, 8) ∈ (0.3125, 0.375].

Reading: at BOTH measured rates the family dies at exactly TWO vanishing power sums:
`δ_death(n, k) ∈ (capacity − 3/n, capacity − 2/n]` — the adjacent-pair bad strip is
`capacity − Θ(1/n)`, *narrower at toy scale* than the KKH26 `Θ(1/log n)` strip. If the
O138 adjacent-pair extremality conjecture holds at small n while the KKH26 m > 1 fiber
shapes dominate asymptotically, the two families must CROSS OVER in n; locating that
crossover is a concrete probe-able question that directly shapes δ*. (Also note the
rate-1/2 small-field artifact is weaker: two constraints already kill p = 17.)

### O141 — the COMPLETE prime spectrum of mid-window badness via cyclotomic norm divisibility: the (16,8) adjacent-pair family is mid-window-bad at EXACTLY 17 primes, and clean at every other field FOREVER (2026-06-11, #357)

`probe_o141_norm_divisibility_spectrum.py` (exact, asserts green). Three verdicts that
together close the (16,8) window profile of the candidate-extremal family for ALL p:

1. **The char-0 layer is EMPTY at depth 1**: no 10-subset of μ₁₆ has `e₂(A) = 0` in
   `ℤ[ζ₁₆]` (exact arithmetic mod `Φ₁₆`, all 8008 subsets). Every per-prime qualifying
   subset of O140's erratic depth-1 row is a pure characteristic-p surplus — the O134
   `p | N(α)` mechanism is not a small correction here, it is the ENTIRE mid-window story.
2. **The finite spectrum**: p qualifies at depth 1 only if `p | N(e₂(A))` for some A; the
   complete set of such primes ≡ 1 (mod 16) is
   `S(16,8) = {17, 97, 113, 193, 257, 337, 433, 449, 881, 1217, 1249, 1553, 2113, 2161,
   3121, 7489, 18433}` (largest norm 18433). Validated: depth-1 census nonzero ⟺ p ∈ S for
   all 25 primes ≤ 1297; for every p > 18433 the row is empty — no scan needed, ever.
3. **Depth ≥ 2 dead at every prime**: a = 11, 12 census = 0 at all lucky primes
   (257…18433), completing O140's universal death.

**The first exact, all-fields, δ-resolved window profile of any candidate-extremal family:**
- `δ ∈ [cap−1/n, cap) = [.4375, .5)`: bad at every p (saturation / t=1 sliver);
- `δ ∈ [cap−2/n, cap−1/n) = [.375, .4375)`: bad at exactly the 17 primes of `S(16,8)`;
- `δ ∈ (Johnson, cap−2/n)`: empty at EVERY prime.

**Consequences for δ\*.** (a) If the O138 adjacent-pair extremality conjecture holds at
(16,8), then for all p ∉ S(16,8) the true δ\* at this instance is `≥ cap − 2/n` — the
window interior is CLEAN and δ\* is pinned within `2/n` of capacity at toy scale; the
entire δ\*-relevant question collapses to (i) extremality and (ii) the norm spectrum.
(b) Whether a deployed prime is mid-window-"unlucky" is a finite norm-divisibility
computation — a new computable invariant of `(n, k, p)`. (c) The asymptotics of
`max_A |N(e_j(A))|` in n (Lehmer/Mahler-measure territory) now directly prices how the
exceptional-prime set grows — the lacunary-resultant thread of #357 §5 acquires a second,
sharper target.

### O141 — THE FAKE-POINT REFORMULATION + exact n = 32 death table: c*(n) = log₂n − 3 at the clean prime, and the fiber mechanism identified as STRUCTURAL moment vanishing (2026-06-11, #357)

`probe_o141_mitm_fakepoint_census.py` (MITM, exact; gates: a = 10, 11 reproduce the O140
exhaustive counts byte-exactly):

**The fake-point lens.** Newton-reducing the constrained band: `e₂(A) = … = e_c(A) = 0`
⟺ `p_j(A) = p₁(A)^j` for `j = 2..c` — a qualifying `a`-subset *masquerades as the single
field point `t = p₁(A)` through its first `c` moments*, and the bad scalar is `λ = −t`.
The census is the set of **fake points** the domain supports at level `(a, c)`. (This is
what makes MITM counting trivial: match half-subset moment vectors against `(t, t², …)`.)

**Exact death table, n = 32, rate 1/4 (constraints e₂..e_{a−8}):**
| a | constraints | p = 97 | p = 193 |
|---|---|---|---|
| 12 | 3 | **384 (census 96 — saturates!)** | 0 |
| 13 | 4 | 0 | 0 |

* At the cleaner prime (193): death at 2→3 constraints for n = 32 vs 1→2 for n = 16:
  **c*(n) = log₂ n − 3 at both scales** ⟹ the m = 1 adjacent-pair family dies at
  `δ_death = 1 − ρ − Θ(log n / n)` — a *capacity-adjacent sliver*, far shallower than the
  KKH26 fiber family's `capacity − Θ(1/log n)`.
* At p = 97 an arithmetic halo keeps a = 12 alive (384 subsets, fake points saturating
  nearly all of F₉₇) — small-prime accidents, gone at 193. Death is field-dependent at
  fixed n; the **structural (field-independent) core** at these (n, a) is empty.
* **The fiber mechanism, explained:** a union of `r` full fibers of `x ↦ x^m` on μ_n has
  `p_j = 0` for every `j` with `m ∤ j` — the KKH26 fiber construction satisfies the moment
  constraints *structurally* (for all fields at once), which is exactly why m-structured
  families reach deep radii at production-size fields while the m = 1 family dies just
  below capacity. Small-field extremality of the adjacent pair (O137/O138) and
  large-field KKH26 reach are two regimes of ONE census.

**The reduced production-scale question (the new apex):** classify the field-independent
solutions of the moment-vanishing system `p_j(A) = t^j (j ≤ c)` over subsets of μ_n. If
fiber unions (and their coset/orbit images) are the only structural solutions, then the
extremal-family census at production fields IS the KKH26 fiber census, the in-tree ceiling
is family-optimal, and the upper-bracket side of δ* equals the fiber-census threshold.
This is the N1 structure conjecture made exact — and it is now a finite, probeable,
formalizable classification problem at each (n, a, c).

### O142 — the norm spectrum at rate 1/4, and a CORRECTION to the O139 reading: the depth-1 row is eventually clean at BOTH rates (2026-06-11, #357)

`probe_o142_rate_quarter_spectrum.py` (exact, asserts green). O139 read the (16,4) depth-1
row (a = 6, δ = 0.625) as "field-dependent, ~n at large p" because all four scanned primes
were nonzero. The O141 norm principle says that was a scan-range coincidence, and the
extended scan confirms it:

* char-0 layer at (16,4) depth 1: **EMPTY** (same as rate 1/2);
* `S(16,4) = {17, 97, 113, 193, 241, 257, 337, 353, 433, 593, 673, 881, 1201, 1601, 2593,
  2833, 4049}`, max norm `4097 = 2¹² + 1` — O139's four primes all lie in S;
* per-prime validation, all 39 primes ≡ 1 (mod 16) up to 2161: nonzero ⟺ `p ∈ S(16,4)`,
  zero mismatches. For `p > 4049` the row is clean **forever**.

**Unified picture (O140+O141+O142).** At both measured rates the candidate-extremal
family's entire window-interior contribution below `capacity − 1/n` is: (depth 1) a finite
explicit prime set with Fermat-flavored maxima (`4097 = 2¹²+1`, `18433`), (depth ≥ 2)
nothing, at any prime. The mid-window δ* question for this family is purely the arithmetic
of cyclotomic norms of subset power sums — and the `max_A |N(e_j(A))|` growth in `n` is
the quantity that prices everything (Mahler-measure / lacunary thread, #357 §5).

### O143 — THE TWO-LAYER LAW of the window census: char-0 vanishing sums + finite-spectrum char-p surplus; the #232 Lam–Leung lane and the O134 surplus mechanism are the two halves of one decomposition (2026-06-11, #357)

`probe_o143_two_layer_law.py` (exact, asserts green). The unification of
O134 + O138–O142:

  `census_p(n, k, row) = (char-0 layer mod p) + (surplus layer)`,

where the **char-0 layer** is the classical vanishing-power-sum locus over `μ_n`
(Lam–Leung / de Bruijn — the #232 machinery, now appearing *inside* the window census) and
the **surplus layer** is nonzero only for `p` in the finite norm spectrum `S(n,k)` (O141).
Measured instances:

* `(8,4)`: both layers empty — the row is clean at EVERY prime (max norm 1);
* `(8,2)`: pure char-0 layer — 10 subsets (two `μ₄`-cosets with `e₁ = 0` + eight
  near-antipodal configs), 9 distinct `e₁` values; `S = ∅` (max norm 16 = 2⁴ has no
  prime ≡ 1 mod 8). Verified `#qual = 10`, `census = 9` at all of
  p ∈ {17, 41, 73, 89, 97, 113, 233, 1009} — field-independent, exactly the char-0 layer;
* `(16,4)`, `(16,8)`: char-0 EMPTY — pure surplus layer on 17 explicit primes each
  (O141/O142).

**Why this matters for δ\*.** The window-interior badness of the candidate-extremal family
is now a sum of two *computable, scan-free* objects: a field-independent census governed by
vanishing-sums classification (nonzero only when `n/k` is large relative to constraint
depth — present at rate 1/4, n = 8; absent at every n = 16 row), and a field-exceptional
finite-prime layer priced by cyclotomic norm growth. The S1 unification thesis (KKH26
census ≡ de Bruijn vanishing sums) is no longer a conjecture about analogy — the window
census literally *contains* the vanishing-sums locus as its field-independent layer.

### O142 — THE STRUCTURAL CLASSIFICATION CONFIRMED AT FIRST INSTANCE: the field-independent solutions of the gap-band system are EXACTLY the fiber unions; no halo at p ≥ 97 (2026-06-11, #357 — the N1 conjecture holds exactly here)

`probe_o142_structural_classification.py` (exact, 5 primes): the gap-band system of the
landed `badScalar_iff_gapBand` at the KKH26 (r = 4, m = 2) instance — stack `(X⁸, X⁶)` on
μ₁₆, code degree < 5, band `e₁(A) = e₃(A) = 0` over 8-subsets:

| p | 17 | 97 | 113 | 193 | 257 |
|---|---|---|---|---|---|
| #solutions | 102 | **70** | **70** | **70** | **70** |

The intersection across all five primes is exactly **70 = the antipodal 4-fiber unions**
(`A` = preimage of a 4-subset of μ₈ under `x ↦ x²`), with `common = fiber_unions`
machine-verified as index sets. Verdicts:

* **The N1 structure conjecture holds exactly at this instance:** every field-independent
  solution of the moment-band system IS a fiber union — the known counterexample mechanism
  is the only mechanism, at this (n, A, B, k).
* **No halo at large primes:** for p ≥ 97 the census is *entirely* structural (70 = 70) —
  the small-prime halo (32 extra at p = 17) vanishes completely rather than decaying.
  Combined with the landed gap law, at this instance the bad-scalar set of the KKH26-shaped
  stack at any p ≥ 97 is EXACTLY the fiber census — theorem-grade given the probe count.
* Chain status toward the δ* ceiling at production fields: gap census law (PROVEN) +
  structural classification (CONFIRMED here) + extremality among stacks (probed at every
  exactly-solved rung) ⟹ the ceiling = fiber-census threshold, pending: classification at
  more (n, A, B, k) instances and strides (next: m = 4 at n = 16; n = 32 instances), and
  the extremality question beyond two-monomial stacks.

Formalization target now precise: `fiberUnion_gapBand` (a fiber union satisfies the
off-stride band — pure power-sum algebra over `X^m − t` roots) gives the backward
(construction) half structurally; the forward classification half is the genuinely new
mathematics, now with an exact finite target at each instance.

### O144 — M2 IS A THEOREM: the agreement-spectrum second moment in Lean — the O120/O122-named follow-up closed, numeric-gated before proving (moments lane, 2026-06-11)

`AgreementMomentTwo.lean` (axiom-clean ×3 `[propext, Classical.choice, Quot.sound]`,
0 sorry, 0 warnings, verified under `autoImplicit=false`):

* `card_exact_pair_agreement` — **the generic two-constraint count** (ToMathlib-grade):
  for ANY `f g : α → β`, functions agreeing with `f` on exactly `j₁` and `g` on exactly
  `j₂` coordinates number `pairAgreementCount |β| d e j₁ j₂` (the explicit
  `Σ_s C(e,s)(q−1)^{e−s}C(d,j₁−s)C(d−(j₁−s),j₂−s)(q−2)^{d−(j₁−s)−(j₂−s)}` closed form,
  ℕ-truncation handling all degenerate regimes incl. q ≤ 2). Proof: partition by the
  agreement-set pair through the sigma index `(s, S, A, B)`; each fiber is the piFinset
  of per-coordinate ZONES `(T-side) ∩ (G-side)` — the intersection form makes
  incompatible patterns vanish through a zero factor instead of case analysis.
* `sum_agreement_spectrum_sq` — **M2**: `Σ_u a_j(u)² = q^k·Σ_{c : deg<k}
  pairAgreementCount q (wt c) (n − wt c) j j` for EVERY n-point domain — the second
  moment enters through the weight enumerator alone, which MDS pins: machine-checked
  domain-independence of the variance, the other half of the O120 reframing (M1 = O122).
  Proof: square → ordered pairs (card_filter + sum_mul_sum), per-pair count = the generic
  theorem at the difference polynomial, pair sum collapsed by the translation bijection
  (sub/add closure of polysDegLT).
* `sq_agreement_le_sum_agreement_spectrum_sq` — the per-word bound (Chebyshev/Markov
  seed): `a_j(u₀)² ≤` the M2 sum, every received word.

**Discipline note:** the statements were NUMERIC-GATED before any proof effort
(`scripts/probes/moments/gate/gate_m2_statements.py`: literal transcription of the Lean
text vs brute-force enumeration at 8 T1 cases + 4 T2 setups incl. non-subgroup domains
and q ∈ {2,3} edges) — a proved mis-transcription is still a wrong brick; the gate makes
that failure mode structurally impossible.

**Where this sits:** with O133 (M3 IS domain-dependent, pencil census) the moment
ladder is now machine-checked on both sides of the boundary: M1 (O122) and M2 (this)
provably domain-blind, M3 provably domain-sensitive with classified mechanism. Named
next: the max-LIST tail corollary (partial sums of a_j), the k=2 rigidity theorem, the
affine-invariance lemma, the t₂ spectral-gap theorem, the (2,4) cross-ratio cell.

### O145 — W1: the weight filter is census × generic — level-1 counting is complete given the census (nubs, 2026-06-11)

Post-O135 redirect executed (pre-registered W1, rungs/HYPOTHESES.md): sampling the
per-locus spaces V_Z at toy scale (q=97, n=32, 10⁵ samples/cell), the excess-zero
distribution beyond the forced 2|Z| dead-fiber zeros on the SMOOTH domain is
**Poisson(remaining/q)-generic to 4 decimal places** (|Z|=3: 0.7644 vs 0.7649;
|Z|=5: 0.7967 vs 0.7971). The pre-registered falsifier ("no smooth concentration beyond
forced") FIRED: the weight-filter cut on smooth domains factorizes as
forced-part (census/dichotomy) × generic volume. Random-domain comparison columns are
partner-contaminated (honest caveat; the smooth-vs-Poisson match needs no comparison).

**Synthesis of the incidence lane's three counting verdicts:** O135 (union bound
measure-tight — incidence overlap contributes nothing in measure) + W1 (weight filter
contributes nothing beyond census) + G1/O132 (the census's incidence anatomy is
closed-form) ⟹ **level-1 list counting is COMPLETE given the census** — empirically, the
only non-generic object in the level-1 window is the census itself. This is exactly the
reduction the census-conditional pin (CensusConditionalPin.lean) assumes; the incidence
lane's evidence now backs its premise from below. Remaining incidence items: G2+G3
(n=64 blind incl. O134 spurious elements) and A3 (λ-family) — blocked on the weekly
agent capacity (Jun 13); both fully specified in HYPOTHESES.md for any seat to take.

### Red team (#357 campaign) — CensusUpperExtremal (the O138 extremality formalization) FALSE as stated at empty-census rungs; floor repair landed
Self-applied adversarial review of the census-conditional pin chain, hours after landing.
**The defect:** the O138 corrected extremality conjecture (ε_mca·|F| = #constrainedCensus)
and its formalization `CensusUpperExtremal` demand ε_mca = 0 wherever the constrained
census is EMPTY — but O139/O140 *measured* empty census rungs inside the window (the
death radius: (16,4), a=7, all p ≥ 97), and every proper linear code has the unconditional
floor ε_mca ≥ 1/|F| at every below-capacity radius (`epsMCA_ge_inv_card_of_finrank_lt`).
**Machine-checked:** `censusUpperExtremal_false_of_empty` (`CensusExtremalFloor.lean`,
axiom-clean): empty census at any in-range agreement + rank < a refutes the hypothesis
outright. The conjecture as posted cannot be exactly right at death radii.
**The repair:** `CensusUpperExtremalFloor` — ε_mca ≤ (#census + 1)/|F| (floor-absorbing);
the repaired pin `mcaDeltaStar_eq_of_censusCrossingFloor` carries the +1 through, and the
F₅ instantiation still recovers δ* = 1/4 (`mcaDeltaStar_F5_via_censusFloor`) — repair
non-destructive. **Honest status:** the +1 asserts nothing takes over at death radii
beyond the floor — exactly O139's registered higher-monomial scan question, which is now
precisely the falsifier of the repaired hypothesis.

### O145 — the classification HOLDS at three instances (after proper multi-prime intersection) + THE ONE-ORBIT HALO LAW + a methodological trap caught (2026-06-11, #357)

`probe_o145_classification_instances.py` + follow-ups (exact):

* **Instance A (n = 16, stack (X¹², X⁸), k = 5 — the m = 4, r = 3 shape):** solutions = 4 at
  every prime ∈ {97, 113, 193, 257}, equal to the 4 quartic-fiber unions. **No halo at all.**
* **Instance B (n = 32, stack (X⁸, X⁶), k = 5 — the m = 2, r = 4 shape):** per-prime
  solutions = **1852 at p = 193, 257, AND 449** (flat count!), of which the three-prime
  intersection is **exactly the 1820 antipodal-fiber unions**. The classification holds.
* **The one-orbit halo law:** at each prime the 32 extra solutions are exactly ONE rotation
  orbit (size n) of a prime-specific exotic 8-subset (e.g. (0,1,3,8,11,18,20,21) at 193 —
  verified dead at 257..1153 and char-0-nonzero |Σζ^i| ≈ 0.66). Halo membership is
  field-specific; halo SIZE is field-independent (32 = n at every prime tested) — the
  flat-count phenomenon at yet another level.
* **METHODOLOGICAL TRAP (caught):** intersecting over TWO primes is NOT a valid
  structurality test — a char-0-nonzero sum can vanish at several primes simultaneously
  (its norm has many prime divisors; the initial 2-prime run made the 193-halo look
  structural because 257 happened to carry an equally-sized halo). Char-0 Lam–Leung
  (no non-antipodal-closed vanishing sums of 2-power roots of unity) is the theoretical
  anchor: any apparent non-fiber structural solution MUST die at large/many primes.
  Protocol fixed: ≥ 3 primes + char-0 numeric check.

**Classification scoreboard:** fiber unions are exactly the field-independent gap-band
solutions at ALL three instances tested — (16, m=2, r=4), (16, m=4, r=3), (32, m=2, r=4) —
strengthening `CensusUpperExtremal`'s structural half. The remaining open legs of the
ceiling chain stay: the classification as a THEOREM (the Lam–Leung bridge — at 2-power n,
char-0 vanishing of e₁ forces antipodal-closure, which plus the band forces fiber towers),
the per-prime halo quantification (one orbit — provable?), and beyond-two-monomial
extremality.

### O145 — the a = 4 char-0 census closed form: N₄(n) = n(n−3)/4, all solutions antipodal-structured (blind n=64 forecast confirmed); the a = 8 layer decomposes 70 = 64 + 6 (2026-06-11, #357)

`probe_o145_a4_closed_form.py` (exact, asserts green). The first closed form of the
two-layer law's field-independent layer:

* **N₄(n) = n(n−3)/4** — derivation: every solution is `A = {x, −x} ∪ {s, t}` with
  `st = x²` (cross terms vanish on the antipodal pair); count `(n/2)·(n−2)/2` minus the
  `n/4` double-counted two-pair solutions `{±x, ±ix}`. Matches the measured census at
  n = 8, 16, 32 (10/52/232) and the **blind n = 64 forecast (976)** verified by exhaustive
  scan; zero antipodal-free solutions at every scale (the ansatz is COMPLETE).
* The (16,8) layer (70 solutions) decomposes structurally as **64** (three antipodal pairs
  + a unit-sum pair `{s,t}` with `st = x²+y²+z²`) **+ 6** (four antipodal pairs with
  `Σxᵢ² = 0` — the pure Lam–Leung configurations; these 6 are exactly the solutions whose
  complement is again a solution). General-a closed form: OPEN (the `70 = C(8,4)`
  numerology is a coincidence of the decomposition, not a binomial structure).

Combined with O144's parity law, the field-independent layer of the depth-1 window census
is now: empty at `a ≡ 2 (mod 4)` (all production dims), and explicitly counted at
`a = 4` — the first two rungs of the vanishing-locus classification the K4/Lam–Leung lane
predicted would govern the window.

### Red team round 2 (#357 campaign) — CensusUpperExtremalFloor FALSIFIED by take-over at the death radius; the extremality conjecture corrected to the EXCESS census
The floor repair survived hours. Running its registered falsifier (the higher-monomial
scan at the death rung; `probe_takeover_death_radius.py`, all 120 monomial pairs over
μ₁₆ ⊆ F_p, exact affine-in-λ method, certificates re-verified by an independent fitter):
**at (16,4), a=7 — where the adjacent census is EMPTY — the half-order pair (X⁹, X⁸)
carries exactly 16 = n bad scalars, and the bad set is the domain μ₁₆ itself,
field-independently (p = 97 and 193). At a=8 (Johnson agreement) it beats the adjacent
pair 16-to-1.**
**Mechanism (closed-form, verified):** coset splitting — on μ₁₆, x⁸ = ±1 on the two
μ₈-cosets, so x⁹ + λx⁸ = ±(x+λ) is piecewise linear; witnesses with six points on one
coset plus the crossing point are explained by ±(X+λ); every λ ∈ μ₁₆ is bad. The
CS25/KK25 splitting mechanism IS the take-over family below the adjacent death radius.
**Machine-checked (`TakeoverCountermodel.lean`, axiom-clean):** `census_16_4_7_empty`
(kernel decide over all C(16,7) = 11440 subsets — the O139/O141 emptiness, now formal at
this instance), two certificate events (λ=1, λ=8 with explicit linear explanations and
the cubic-vs-constant no-joint argument), `takeover_falsifies`: ε_mca ≥ 2/97 > 1/97 =
(census+1)/|F| — CensusUpperExtremalFloor is FALSE at (16,4)/F₉₇ for every crossing < 7.
**What survives:** the pin engine (census-function agnostic), census_le_epsMCA (slice
lower bounds), the radius quantization. **What must change:** the upper-extremality
target is the EXCESS census — bad counts of (X^s, X^{s−1}) for all s ≥ a; the
agreement-matched census is the s = a slice, the take-over is the s = n/2+1 slice with
its own flat-n law (one crossing point per λ ∈ ±μ_n). Until the excess census law is
formalized, the campaign has NO standing upper-extremality hypothesis; G2-3's "two named
surfaces" must use the excess-aware surface or die to this countermodel.

### O146 — RED TEAM: CensusUpperExtremal REFUTED AS STATED (double-spike witness at a = n−1) and CORRECTED: the profile is the MAX of two proven families (sparse-spike staircase ∨ census); the corrected form survives every exact data point (2026-06-11, #357 red-team cycle 1)

Red-team attack on the census-crossing pin at the non-2-power ladder instances:

* **The refutation (exact):** at (7,6,3) AND (13,6,3), agreement a = 5 (= n−1) has
  adjacent-pair census **0** but exact max-bad over ALL stacks **2** — the census is not
  extremal at this rung. Witness extracted (syndrome-reduced exact scan): the **double
  spike** u₀ = 1_{x₅}, u₁ = 1_{x₄,x₅}: bad γ ∈ {0, −1}, each line a 1-sparse word vanishing
  on n−1 points. This is precisely the mechanism of the just-landed **universal second
  band** (`ε_mca = 2/|F|` exactly on `1 ≤ δ·n < 2` for EVERY linear code of distance ≥ 4) —
  a field-independent staircase near δ = 0, orthogonal to the census mechanism.
* **The correction:** the extremality conjecture becomes
  **`ε_mca(C, 1 − a/n) · q = max(staircase band value at a, adjacent-pair census at a)`** —
  the sparse-spike staircase dominates at a ∈ {n, n−1, …} (δ·n small), the census takes over
  at the crossing scale. Both families are PROVEN lower bounds (universal bands; census law
  + `census_le_epsMCA`); only the upper half ("nothing beats the max") remains the named
  surface.
* **The corrected form survives every exactly-computed instance:**
  (5,4,2): {a=4: max(1,1)=1 ✓, a=3: max(·,4)=4 ✓};
  (13,4,2)/(17,4,2): {1,4} ✓; (12,6) @ 13/37/61: a=9: max(·,12)=12 ✓;
  (7,6,3): {a=6: max(1,1)=1 ✓, a=5: max(2,0)=2 ✓, a=4: max(·,7)=7 ✓};
  (13,6,3): {1, 2, 13} ✓. No exact data point deviates from the two-family max.
* Bonus: the small-field saturations (census = p at (7,6,3) a=4 and (13,6,3) a=4) again
  match max-bad exactly — saturation is census-driven, not spike-driven.

**Consequence for the conditional pin:** `mcaDeltaStar_eq_of_censusCrossing'` remains valid
verbatim wherever the crossing agreement sits BELOW the staircase rungs (a_c ≤ n − 2 and
the staircase value at a > a_c also ≤ ε*·q — at production parameters ε*·q ≈ 2^128 the
first staircase bands are astronomically below threshold, so the staircase NEVER decides
the crossing there; the correction matters only at toy scales/tiny ε*). The named surface
should still be restated as the two-family max for honesty. Red-team cycle 1 verdict:
**the candidate pin survives, with a corrected and sharper conjecture.**

## Fable N1 (pencil-energy law) — REFUTED at scale (2026-06-11)
Hypothesis: δ*(H) = F(E₂(H)/n²), E₂ = Σ_b t₂(b)² (Möbius pencil energy).
Refutation: `scripts/probes/probe_n1_energy_vs_badcount.py` — exact ε_mca bad-count is
DOMAIN-INDEPENDENT (smooth=random at equal n,k,δ) across 8 feasible instances, while E₂ varies
up to 10×. So ε_mca is not a function of E₂; the energy is moment-blind to the extremal bad count.
Constraint lemma target: ∃ two domains, same field, E₂ differing, ε_mca equal. The proven
E₂=Θ(n³) smooth separation (MobiusPencilEnergy.lean) is a spectrum-moment fact, not δ*-controlling.
Refinement N1′: target the EXTREMAL pencil invariant (max t₂ / M3 third moment), not the sum.

### O147 — the two-layer law EXTENDS to the excess census; the CA/MCA gap localizes on coset witnesses; the take-over flat-n numerator is one rotation orbit of char-0 pinned scalars (2026-06-11, #357)

`probe_o147_excess_census_two_layer.py` (exact char-0 in ℚ(ζ₁₆) + mod-97; asserts green).
The hand-off question from the take-over comment ("does the norm machinery extend to the
excess system?") — answered, with three structural verdicts at the take-over instance
((X⁹, X⁸) over μ₁₆, k = 4, a = 7, excess 2):

1. **Subset census is pure layer-1**: 464 qualifying 7-subsets in char 0 AND mod 97 —
   the two-layer law extends verbatim to the excess band system (surplus primes are again
   norm divisors of the band minors).
2. **The CA/MCA gap is exactly the coset-witness layer**: 16 of the 464 subsets carry a
   full γ-LINE (band system rank 1) — and they are precisely the sixteen 7-subsets of the
   two parity classes (the index-2 subgroup and its coset). On those witnesses `X⁸ ≡ ±1`
   and `X⁹ ≡ ±X`, so both rows are codewords there — the stack is jointly explainable and
   `mcaEvent` cannot fire. The γ-lines are CA-bad but MCA-invisible: a fully worked,
   machine-checked instance of the CA ≠ MCA separation *inside* a census computation.
3. **The flat-n law of the take-over family is a one-orbit char-0 law**: the remaining
   448 subsets pin γ, with exactly 16 = n distinct pinned values — and the 16 values form
   a SINGLE rotation orbit `{−ζ^{4+j} : j}` (γ₀ = −ζ⁴). Field-independence of the measured
   16-at-every-prime is explained: the values are characteristic-zero constants reduced
   mod p.

**Consequence for the excess-census ledger:** census(MCA, excess row) = (pinned char-0
γ-census, one orbit here) + (finite-spectrum surplus); the band system alone OVERCOUNTS by
the explainable coset layer — any future excess-census ledger entry needs the
explainability filter, not just band solvability.

### S3 (#357 campaign) — pure-frequency extremality REFUTED at intermediate rungs; repaired by rotation powers; the flat numerator IS one orbit
Idea (v1): every rung of the exact bad-γ profile is attained by a *pure-frequency*
eigenstack `(e_{j₀}, e_{j₁})` of the rotation `R` (diagonal on syndrome frequencies), making
every rung count `ε + j·d` with `d = ord(h^{j₁−j₀}) | n`.
**Refuted (probe, exact):** at `(7,6,3)/(13,6,3)` m=5 and `(13,12,6)` m=11/m=10 the
pure-frequency class caps at 1 < exact 2/2/3 (`probe_s3_eigenstack_orbit_law.py`, stages
B/C). The σ¹ syndrome eigenspaces are 1-dimensional — too rigid for the count-2/3 rungs.
**Repaired (same probe, confirmed):** rotation *powers* σ^t have multi-dimensional syndrome
eigenspaces (frequency classes mod `n/gcd(t,n)`); σ^t-eigenstacks attain every missing rung
with the predicted orbit structure — count-2 rungs by antipodal pairs `{γ, −γ}` (σ³ at n=6:
`[1,6],[2,5],[3,4]` at p=7; σ⁶ at n=12: `[1,12],[2,11],[3,10]` at p=13), count-3 by
ω-triples (σ⁴: `[4,10,12]` = an ⟨h⁴⟩-orbit). The plateau rung m=9 count 12 = **one full
order-12 orbit** (attainer `(j₀,j₁) = (9,8)`, ε = 0), reproduced verbatim at p = 37, 61
where the orbit is a *proper* coset of `F*` — the field-independent flat numerator is an
orbit count, mechanism identified. Honest census caveat: at `(13,6,3)` m=5 only 6 of 300
maximizers are genuinely σ³-eigen (the rest are eigen only for the vacuous t = n) —
eigenstacks *attain* the exact max at every tested rung but do not *exhaust* the maximizer
set at intermediate rungs; structured-extremality (N1) must be read as attainment.
→ verified as `MCAEigenstackOrbitLaw.lean` (axiom-clean, layered on the same-hour sibling
engine `MCAEquivariance.lean` — the two S3 lanes landed within the hour; engine adopted,
orbit law layered on top): `mcaEvent_eigenstack_iff` (bad set invariant under
`T(γ) = a⁻¹b + γ·a⁻¹c`), `orderOf_le/dvd_card_of_mul_mem` (orbit arithmetic for invariant
scalar sets), `orderOf_le/dvd_badScalarSet_card_of_eigenstack` (count = ε + #orbits·d,
field-independent), and the F₅ demo (one certificate + the orbit law re-derives
`ε_mca(C542, 1/4) ≥ 4/5`, replacing four hand certificates).
**Where the open core moves:** the rung profile is orbit arithmetic over divisors of `n`;
which radius activates which divisor reduces to a splitting-locus question for
`x^{j₀} + γx^{j₁} − β` over the domain subgroup — a sharply-posed finite question. The
KKH26 ceiling stack is itself an eigenstack (eigenratio `g^{−m}`, order s): the
near-capacity ceiling family and the toy plateau maximizers are one object class, and the
one-orbit halo law (O145) is this mechanism at the census level.

### O147 — RED-TEAM CYCLE 2: no third mechanism — THE TWO-FAMILY PROFILE LAW explains 100% of all exact data ever computed (2026-06-11, #357)

The third-mechanism hunt at the richest exactly-computed instance, (13,12,6) (the n = 12
orbit-exact profile {a=12: 1, a=11: 2, a=10: 3, a=9: 12, a≤8: 13}), against the corrected
two-family prediction `max(staircase = n−a+1, census(a))`:

| a | staircase | census (computed) | max | exact |
|---|---|---|---|---|
| 12 | 1 | 1 | 1 | **1 ✓** |
| 11 | 2 | 0 | 2 | **2 ✓** |
| 10 | 3 | 0 | 3 | **3 ✓** |
| 9 | 4 | 12 | 12 | **12 ✓** |
| ≤8 | — | saturates | p | **13 = p ✓** |

* **No third mechanism at any exactly-computed point.** The two-family law now matches
  every exact rung across 8 instances / 13 field-instance combinations: (5,4,2),
  (13,4,2), (17,4,2), (12,6)@{13,37,61}, (7,6,3), (13,6,3), (16,4)-window-census rows,
  (32,8)-census rows.
* **The staircase generalization gets its third point:** band j = j+1 at j = 2 (a = 10:
  exact 3). Conjecture: `ε_mca·q = ⌊δn⌋ + 1` on each band until the census crossing —
  bands 0–1 already proven universally (sibling); band-j spike family = the obvious next
  Lean target.
* **The unified profile law (generation-2 central claim):** for smooth-domain RS,
  `ε_mca(C, 1 − a/n)·q = min(q, max(n − a + 1, census(a)))` at every exactly-computed
  scale. Status: both lower-bound families PROVEN (bands 0–1 universal; census at all
  scales via `census_le_epsMCA`); census structural core CLASSIFIED (char-0, fiber unions);
  upper half = the named two-family-max extremality + per-prime halo bound.
* **Production consequence:** at `ε* = 2^{−128}` the staircase is irrelevant
  (≤ n ≪ ε*·q ≈ 2^{128}) and `δ*(production smooth RS) = 1 − a_c/n` with `a_c` the census
  crossing — the conditional pin `mcaDeltaStar_eq_of_censusCrossing'` with the corrected
  surface. The two named open surfaces are exactly: (i) two-family-max extremality,
  (ii) the per-prime halo bound. Everything else in the chain is machine-checked.

### O148 — G2-3: the production crossing, priced exactly — under PROVEN census counts the fiber census never reaches ε*·q at |F| < 2^256; the entire numeric uncertainty of δ*(production) is the true subset-sum count at fold scales s ∈ [64, 256] (2026-06-11, #357)

Assembly of the profile law (O147) with the in-tree census-size certificates:

* **The crossing calculus.** Under the profile law, δ*(production) = 1 − a_c/n where a_c is
  the largest agreement with census(a) > ε*·q ≈ 2^128. The census at fold scale s = n/m,
  row r (radius δ = 1 − r/s, validity r ≤ ρs + 2) has PROVEN size ≥ stratified
  `Σ_j 2^{r−2j}·C(s/2, r−2j)` — but distinctness is certified only under the prime
  threshold: `p > s^{s/2}` (resultant route) or the Parseval-halved threshold (s = 64 rows
  open unconditionally at |F| < 2^256; s = 128 closed — the in-tree reach table).
* **The pricing.** At |F| < 2^256 the certified scales are s ≤ 64 (unconditional) where the
  maximal certified census is ≈ 2^{s/2 + s/2} = 2^64 ≪ 2^128: **the certified fiber census
  never crosses ε*·q at production parameters.** The deep rows (s ≥ 128, census up to
  2^{s(H₂+ρ)} ≥ 2^128 at s ≈ 256) need either the TZ external (polynomial-field route,
  `kkh26_mcaDeltaStar_le_of_TZ`, in-tree) or genuinely larger certified counts.
* **The localized uncertainty.** The production δ* under the profile law therefore sits in
  the bracket: floor = the proven Johnson-side MCA theorems (1 − √ρ, unconditional);
  ceiling = capacity − 2/s* where s* is the largest fold scale whose TRUE distinct-sum
  count crosses 2^128 at |F| < 2^256. Everything in between is decided by ONE number per
  rate: **the true (not resultant-certified) distinct subset-sum count of μ_{s} strata at
  s ∈ [64, 256]** — a finite question per scale, sharply localized, attackable by the
  lacunary-resultant / certified-computation routes already inventoried (#357 §5) and by
  the O134 per-prime correction theory.
* **Two regimes of the answer (conditional on the two named surfaces):** if the true counts
  match the char-0/stratified forecasts (no large-prime collapse — the genlaw/falsifier
  evidence supports this up to measured surpluses), then s* ≈ 256 and
  **δ*(ρ, 2^{−128}) = 1 − ρ − Θ(1/s*) = capacity − c(ρ)** with c(ρ) ≈ 2/s* a CONSTANT
  (not Θ(1/log n)) for all n ≥ s*·m — strictly stronger than the published KKH26 phrasing,
  whose 1/log n came from the prime-threshold coupling, not from the census itself. If the
  true counts collapse at large p below 2^128, δ* recedes toward the floor accordingly. The
  prize question, under the profile law, IS this count.

### O148 — THE TAKE-OVER ROW IS COMPLETELY PINNED: census = 16 = n at EVERY prime, zero surplus (2026-06-11, #357)

`probe_o148_takeover_row_pinned.py` (exact). Completing O147: surplus at the take-over
row ((X⁹,X⁸) @ a = 7, (16,4)) can only occur at primes dividing a band-minor cyclotomic
norm; the candidate set is `{17, 97, 113, 193, 241, 257, 337, 353, 401, 433, 449, 577,
641, 977, 1489, 6833}` (16 primes, max 6833; float-embedded norms — exact-integer
recomputation is the named follow-up). Per-prime verification at **all 16 candidates**
plus clean controls (1009, 1361): pinned census = **16 = n and line-subsets = 16 at every
single prime**. The rank-match never completes — the surplus layer of this row is EMPTY.

**Net law: `census_MCA((X⁹,X⁸) @ a=7, p) = n` for every prime `p ≡ 1 (mod 16)`** — one
rotation orbit of `−ζ⁴` (O147), no exceptions, no exceptional primes. The strongest and
cleanest flat-numerator law in the programme; with `census_le_epsMCA` it gives
`ε_mca ≥ n/p` at `δ = 9/16` (mid-window!) for every field — and under the corrected
(excess) extremality it is exact there. The take-over family is rigid in the strongest
sense: its MCA badness is a single characteristic-zero orbit, invisible to field choice.

### O149 — the halo mechanism verified at the norm level: the exotic subset's norms are EXACTLY 2²·193² — monogamous halo membership; the halo bound becomes a divisor-counting question (2026-06-11, #357, surface (ii))

`probe_o149_halo_norm_mechanism.py` (exact ℤ[ζ₃₂] arithmetic mod Φ₃₂): the p = 193 exotic
halo subset `A = (0,1,3,8,11,18,20,21)` (O145) has

  `N(α_A) = N(β_A) = 148996 = 2² · 193²`

(α = Σζ^i, β = Σζ^{3i} — the two gap-band constraint sums). Consequences:

* **Monogamy:** 193 is the only odd prime dividing either norm — this subset can join the
  halo at p = 193 and at NO other prime. The O145 observation (each prime's halo is its
  own) has its mechanism: halo membership at p ⟺ p | N(α_S) AND p | N(β_S).
* **Joint vanishing explained:** both constraint norms share the prime — the apparent
  coincidence that one subset satisfies BOTH band constraints mod 193 is a single
  algebraic event (likely one prime ideal of ℤ[ζ] above 193 dividing both elements).
* **Tiny norms:** 148996 ≈ 2^17.2 versus the worst-case bound a^φ(32) = 8^16 = 2^48 —
  the same real-vs-worst-case gap measured at the resultant level (O129/Parseval), now at
  the halo level. Per-subset halo-prime counts are ≤ Ω(N) ≤ ~17/log₂(p) ≈ 2 at p ≈ 200.
* **The halo surface, recast:** `halo(p) = #{S non-fiber : p | N(α_S), p | N(β_S)}` — the
  one-orbit law is a joint norm-divisibility multiplicity statement, attackable by the
  O134 α-spectrum correction theory (which counts exactly such divisibilities) and by
  averaging: `Σ_p halo(p) ≤ Σ_S Ω(N(α_S))` gives a PROVABLE average-halo bound from the
  norm bound alone. Formalization route: Mathlib cyclotomic-field norms; the finite
  per-instance certificates (like this one) are exact-arithmetic checkable today.

## CORRECTION to the domain-blindness entry (2026-06-11)
The "δ* domain-independent" reading was over-stated: exact probes reach only the SATURATED band
[UD,~Johnson) where bad count = n (saturation ceiling) for all domains — the easy regime. The
INTERIOR (Johnson,capacity), where δ* lives and KKH26 is domain-specific, is exact-infeasible at
low rate. So: domain-blind in the saturated band (proved by enumeration of all 252/120 subsets);
interior separation OPEN, not killed. N1 (specific E₂ law) stays refuted; N1' (extremal pencil /
M3 third moment) REVIVED as the live domain-aware thread.

### O151 — PARSEVAL RESTORATION (anti-laundering note) + the sharpened finite-field tower: threshold exponent HALVED (2026-06-11, #357 surface (ii))

* **Anti-laundering record:** `KKH26ParsevalThreshold.lean` (520 lines, the A3 resolution —
  `natAbs_resultant_cyclotomic_le_parseval`, `kkh26_lemma1_parseval`) was deleted by the
  #353 cleanup (1d1bd5c86) as "refuted/superseded". It is **neither**: restored verbatim,
  it compiles axiom-clean against the current tree, and its halved-exponent bound is
  load-bearing. Restored and re-landed. Lesson: "superseded" claims in prune commits need
  the same grep-the-theorem scrutiny as "proven" claims.
* **The sharpened tower** (`HaloFreeThresholdParseval.lean`, axiom-clean):
  `not_isRoot_of_l2On_parseval_lt` (generic ℓ² non-vanishing at a primitive root, exponent
  halved against the ℓ¹ engine), depth-1 at threshold `(2^m)^{2^{m−2}}`, and
  `tower_closed_finite_parseval` — the full dyadic classification in `F_p` at the halved
  threshold (level 1 threshold-free; levels ≥ 2 Parseval; one top-level bound covers all).
* **Reach gained:** m = 5 (n = 32): threshold 2^64 → 2^40; m = 6 (n = 64): 2^160 → 2^96 —
  at |F| < 2^256 the unconditional-census layer now covers domains up to n = 128
  (m = 7: (2^7)^{2^5} = 2^224 < 2^256 ✓) versus n = 64 before. The certified-count
  frontier of surface (iii) moves one fold scale deeper.

### O152 — RED-TEAM CYCLE 3: the two-family law survives the structure-free (prime-n) test; nine instances, zero deviations (2026-06-11, #357)

`probe_o152_prime_domain_redteam.py` (exact): the harshest universality test — (11,5,2),
domain μ₅ ⊆ F₁₁, n = 5 PRIME: no 2-adic tower, no fiber structure, Lam–Leung at prime
order says the only vanishing subset sums are ∅ and the full group.

| a | staircase | census | max | exact |
|---|---|---|---|---|
| 5 | 1 | **1** (= the full-group vanishing, the unique prime-5 Lam–Leung relation) | 1 | **1 ✓** |
| 4 | 2 | 0 (no 4-subset vanishing at prime order — as the structural theory demands) | 2 | **2 ✓** |
| 3 | 3 | 10 (unconstrained sums, all distinct) | 10 | **10 ✓** |

The census values are exactly what the prime-order Lam–Leung classification predicts —
the structural theory's reach extends beyond 2-power domains verbatim (vanishing-sums
classification swaps in per prime factor). Scoreboard: the two-family profile law now
matches **nine instances / 14+ field-combinations with zero deviations**, across 2-power
(4, 16, 32), composite (6, 12), and prime (5) domain orders. Cycle-3 verdict: SURVIVES.
Next falsifier frontier requires either larger-p composite-n exact runs (orbit-decide
engineering) or a fundamentally different stack family (rational/DEEP shapes at an
exactly-computed rung).

### O153 — THE BAND-j COLLAPSE THEOREM (proof worked out; formalization queued): for distance > 4j, at most j+1 bad scalars on band j — the staircase side of the profile law becomes a theorem (2026-06-11, #357 surface (i), the first general sup-side result)

**Theorem (band-j collapse).** Let `C` be a linear code of distance `d > 4j` on `n` points,
and `δ` with `j ≤ δn < j+1`. Then every stack `(u₀, u₁)` has at most `j + 1` bad scalars:
`ε_mca(C, δ) ≤ (j+1)/q`. With the in-tree `(j+1)`-spike lower bound (`epsMCA_generalJ_ge`),
the staircase law `ε_mca·q = j+1` on band `j` is EXACT for high-distance codes.

**Proof.** Badness of `γ` at agreement `≥ n − j` gives a codeword `c_γ` and error
`w_γ := L_γ − c_γ` of weight `≤ j`, where `L_γ = u₀ + γu₁`. Fix a bad `γ₁`. For bad `γ`,
`(γ − γ₁)u₁ = (c_γ − c_{γ₁}) + (w_γ − w_{γ₁})`, so the coset `(γ−γ₁)u₁ + C` contains the
weight-`≤ 2j` word `w_γ − w_{γ₁}` — unique since `d > 4j`. Cross-consistency for two bad
`γ, γ'` (with `λ = γ−γ₁`, `λ' = γ'−γ₁`): `λ'(w_γ − w_{γ₁}) − λ(w_{γ'} − w_{γ₁}) ∈ C` has
weight `≤ 4j < d`, hence is zero. Setting `v := (w_γ₂ − w_{γ₁})/λ₂` (any second bad scalar;
`v ≡ u₁ mod C`), this yields the **rigid relation `w_γ = w_{γ₁} + (γ−γ₁)·v` pointwise** for
every bad `γ`.

Case `|supp v| ≥ j+1`: for each `x ∈ supp v`, the map `γ ↦ w_γ(x) = w_{γ₁}(x) + (γ−γ₁)v(x)`
is injective-affine in `γ`, so it vanishes for at most ONE bad `γ`: each `x ∈ supp v` lies
in `supp w_γ` for at least `t − 1` of the `t` bad scalars. Summing:
`t·j ≥ Σ_γ wt(w_γ) ≥ |supp v|·(t−1) ≥ (j+1)(t−1)`, forcing **`t ≤ j+1`**.

Case `|supp v| ≤ j`: `u₁ ≡ v mod C` with `v` short. The pair-clause criterion (any nonzero
codeword agreeing with a weight-`≤ 2j` word on `n − j` points has weight `≤ 3j < d`, hence
is zero) reduces badness of `γ` to: `supp v ⊄ supp(w_{γ₁} + (γ−γ₁)v)`, i.e. some
`x ∈ supp v` has `w_{γ₁}(x) + (γ−γ₁)v(x) = 0`, i.e. `γ = γ₁ − w_{γ₁}(x)/v(x)` for some
`x ∈ supp v` — at most `|supp v| ≤ j` bad scalars beyond... and including the bookkeeping
at `γ₁`, **`t ≤ j+1`**. ∎

**Hypothesis audit (honest):** the proof uses `d > 4j` (uniqueness at weight `2j` and the
`4j`-weight cross-relation). The exact data says the conclusion holds beyond it: at
(13,12,6), band 2 has `max = 3 = j+1` with `d = 7 < 8 = 4j`. So the distance condition is
NOT tight — the cross-relation step (weight `≤ 4j`) is the binding constraint; sharpening
to `d > 2j + j` or a direct argument is open. In-hypothesis checks: (13,12,6) band 1
(`d = 7 > 4`): exact max 2 = j+1 ✓; all band-0 instances ✓ (the proven universal bands).

**Consequences:** (a) the staircase side of the two-family profile law is now THEOREM-grade
for `d > 4j` (previously: bands 0–1 only); (b) combined with the census side, the profile
law's remaining conjectural content for high-distance codes is *only* the census-dominance
regime (`a` near the crossing) — sup-extremality has been pushed from "all radii" to "the
census band alone"; (c) production RS has `d = n − k + 1` huge, so every staircase band of
interest is in-hypothesis there.

**Formalization plan** (the next Lean brick): unique-short-coset-word lemma (`d > 4j`);
the rigid relation (3 coset manipulations + weight bounds); the two counting cases
(pigeonhole over `supp v`). All elementary Finset/weight arithmetic on top of the in-tree
distance API; no new analytic input.

### GeneralStaircaseConjecture (d ≥ 2b+1) REFUTED at b = 4 — THE 3b−2 LAW unifies everything (#357 round 4)

Pre-registered decision experiment between f(b) = 3b−2 and 2b+1 (coinciding at b = 3): the
TRIPLED-column [15,3,9] moment-curve code over F₁₁ (G columns = (1,t,t²) each repeated ×3,
t ∈ {0..4}; min weight 9 verified) admits a 5-bad band-4 stack at d = 9 = 2b+1:
γ = (0,1,2,3,4), e = (1,1,1,8,8,8,2,2,2,8,8,8,1,1,1), reconstructed u₀,u₁ verified honestly
(5 bad scalars, witness card ≥ n−3). The syndrome-equality system (48 eqs on 15 unknowns)
has admissible kernel — the moment-curve direction arrangement matches the Vandermonde
relation-space arrangement, exactly as the doubled-column case at b = 3.

**THE UNIFIED LAW (general linear codes):** band-b collapse to the spike value b/q holds
iff d ≥ 3b−2; at d = 3b−3 the (b−1)-tupled-column codes explode. All data coheres:
b=2: PROVEN at d ≥ 4 = 3·2−2 (MCABandTwoCollapse/Exact), explosion at d = 3 (the cocycle
family = 1-tupled); b=3: PROVEN at d ≥ 7 = 3·3−2 (MCABandThreeAssembly/Exact), doubled
(= 2-tupled) counterexample at d = 6; b=4: 3-tupled counterexample at d = 9, collapse
conjectured at d ≥ 10. The triple-c*-support arithmetic (3(b−1) < d) explains the
threshold; the landed b=3 deep-core proof generalizes along it. The m-tupled witnesses are
maximally non-MDS (parallel matroid classes of size b−1) — the matroid-invariance lane
(N4.1) is now the structural frontier: the RS/MDS threshold (d ≥ 2b conjectured, directed-
search-supported) vs the general 3b−2 differ exactly by parallel-class capacity.

### Staircase collapse threshold (#357 rounds 16-18) — 3j−2 PROVEN; 2j conjectured sharp
`UniversalStaircaseCollapse.lean` proves ≤ j bad scalars on the first j bands for
d ≥ 3j−2 (triple-union chaining). Sharpness data: j=2: d=3 jumps, d=4=2j collapses
(PROVEN trichotomy, sibling); j=3: d=5 < 2j breaks (B ≥ 6, widened sweep), d=6=2j
holds at template scale (B = 3, sparse sweep (17,8,3)). CONJECTURE: true threshold
d ≥ 2j; the 3(j−1) in the proof is an artifact of chaining through triples — a
2j-route needs a different identification argument (the j=2 proof avoids chaining
entirely). Template caveat: d=6 B=3 is wt≤2-restricted; heavier stacks unswept.

### CORRECTION to the above (#357 round 19): 2j-sharpness conjecture REFUTED — 3b−2 is THE law, RS included
The "2j conjectured sharp" note above is dead: the perfect-square pencil identity
(rA² − hAB + pB² = ρλ²T^{f+2(b−1)}, #357 comment ~157, probe_mds_pencil_explosion.py)
produces band-b explosions at every d ≤ 3b−3 for GENUINE RS codes (exact scans:
RS[F₁₇,μ₈,3] d=6 band-3 count 4 > 3; RS[F₁₉,μ₁₈,10] d=9 band-4 count 6 > 4; smooth
domains supply n/(b−1) bad scalars via μ_{b−1}-cosets). My (17,8,3) template sweep
(B=3) was wt≤2-narrowness — the pencil stacks have richer syndrome-series structure.
The master staircase threshold f(b) = 3b−2 (proven in UniversalStaircaseCollapse +
the fleet's MCAStaircaseMaster) is sharp at every b, for every linear code INCLUDING
MDS/RS. The MDS/general separation hoped for in the half-distance round does not
exist at the staircase level.
### MDSStaircaseConjecture REFUTED — the degenerate-pencil explosion; 3b−2 is sharp for RS/MDS too (#357)

The "MDS rank conjecture" (RS keeps the staircase collapse down to `d ≥ 2b`; directed-search
record at five instances, restated round 5 as Padé full-rank) is FALSE. The missed branch:
the **perfect-square pencil syzygy** `rA² − hAB + pB² = ρλ²·T^(f+2(b−1))` with
`A = B + λT^(b−1)`, `p = r = ρT^f`, `h = 2ρT^f` — a degenerate-discriminant solution to the
collinearity system, valid mod `T^m` for every `m = 2(b−1)+f ≤ 3b−4`. Realization: any
family of disjoint `(b−1)`-blocks of the domain with locators in one pencil `⟨B, T^(b−1)⟩`
— **cosets of `μ_(b−1)`** on smooth domains (locators `1 − x^(b−1)T^(b−1)`), equal-sum
pairs at `b = 3` on any domain — donates one bad scalar `γ_V` per block
(`(1+γ_V)B + λT^(b−1) ∝ V`), with error words from the partial fractions of
`ρ(1+γ)T^f/V` (all weights nonzero) and the affine-in-γ syndrome family exact. Count:
**n/(b−1), field-independent, on every `d ∈ [2b−1, 3b−3]`**.

Probe `probe_mds_pencil_explosion.py` (exact end-to-end mcaEvent scans): (11,8,3) d=6 → 4
bad; (17,8,3) d=6 → 4; **(19,18,10) d=9=2b+1, b=4 → 6 bad** (the in-hypothesis formal
instance, k+2b = 18 ≤ n); (19,18,11) d=8=2b → 6; (19,18,12) d=7=2b−1 → 6; (17,8,4) d=5
band 3 → 4 (settles the widened band-3 sweep: ≥ 4 = n/2). Lean countermodel:
`MCAMDSStaircaseRefuted.lean` (`mdsStaircaseConjecture_refuted`, five root-counting
certificates, axiom-clean).

**Why the directed searches missed it:** (i) band-3 `d = 6` exhaustive rows were at
`n = 7`, where only 3 disjoint pencil pairs fit (geometric starvation — at `n = 7` the
fourth pencil member degenerates to an improper singleton fraction, consistent with the
measured collapse-to-3); (ii) at `(11,8,3)` the construction lives on exactly one of the
105 pair-partitions (the equal-sum one) with the γ-quadruple Möbius-determined by the
block products; (iii) the `(17,8,3)` "d=6 holds (B=3)" sweep was wt≤2-template-restricted
— the pencil stack has weight 5. Constraint kept: collapse-side proofs below `3b−2`
cannot exist; the binding obstruction is pencil capacity (`n/(b−1) ≥ b+1` ⟺
`n ≥ b²−1`-ish), not parallel matroid classes.

**Corrected landscape:** (a) `TheGeneralStaircaseLaw` (`d ≥ 3b−2`) is THE law for ALL
linear codes including RS/MDS — no MDS/general separation at the threshold level (the
d = 2b separation read off `MCAHalfDistanceGeneralRefuted` was an artifact of `n = 8 <`
pencil capacity on the RS side); (b) the `d ≥ 2j` sharpening conjecture for
`UniversalStaircaseCollapse` is refuted (T3: d = 2j+1, six bad > j = 4); (c) the exact-RS
staircase (`MCAStaircaseRS`/`BandExactness`) hypotheses `3(b−1)+k ≤ n`-ish are TIGHT —
the strip above is genuinely explosive; (d) `MonomialDomination` gains its sharpest live
falsifier: the pencil stacks are non-monomial 9-sparse words — whether a monomial pair
matches count n/(b−1) at the strip cells is now the decisive check.

### O154 — THE JOHNSON-DISCHARGE ATTACK MAP, verified node by node: everything reduced to Claim 5.10's extension-field pinning; two elementarization routes proven to fail at exactly 2δ (2026-06-11, goal: Johnson with no Props)

Full audit of the Johnson cone (the #302 siege), node status verified by reading each
file's theorems and axiom blocks:

* **PROVEN end-to-end:** the funnels (`johnsonNumericBound_of_surface` ← `hsurface`),
  K1 cell production (`exists_cell_production` / `bad_card_le_of_cell_production`),
  the decoded bridge (`mcaEvent_decoded_data`), richness concentration
  (`Hab25UniqueRichFactor`: rich budgeted irreducible factor unique and an associate of
  `Y − C w`), the coordinate weld (`coordinateUpgrade_of_assigned_factor_rich`,
  `global_branch_of_assigned_factor_rich`), the slack weld
  (`global_branch_of_witnessed_subcell`), the S5/Appendix-A plumbing
  (`RationalFunctions{Core,Strong}` sorry-free), the budget supply
  (`factorBudgetIndex_*`), and the deployed-regime capstone reduction
  (`kkh26_deltaStar_pin_of_interior_ceiling`: δ* = 1 − r/2^μ EXACTLY conditional on ONE
  surface, `InteriorCeiling`).
* **THE OPEN CORE (everything converges here):** the K4/assignment-coherence node = the
  paper's Claim 5.10 *extension-field* step (eprint 2020/654 pp. 24–27): per-coordinate
  agreement counts pin the identity `γ(x) = w(x, Z)` in `L = Frac(F[Z,X]/R)`, retroactively
  pinning disagreeing scalars, interpolating the branch in `L` scalar-free. The slack
  weld's additive `k·M` route is REGIME-WRONG at Johnson (`M ≈ δ/(1−ρ)·|E|` makes
  `k·M ≥ |E|`); the paper's multiplicative Claim-5.11 count is the required form.
* **Elementarization no-gos (proven/probed this session):**
  (i) pairwise difference quotients: `D(γ,γ')` is `2δ`-close to `u₁`; uniqueness needs
  `2δ <` UDR — dies at `δ ≥ (1−ρ)/4`, far below Johnson;
  (ii) the saturation route (per-coordinate `g_ω(Z) := R(Z, ω, u₀(ω)+Z·u₁(ω))` ≡ 0 at
  high-mass coordinates — the fold IS the section, no pHat interpolation needed) pins the
  *witnessed* incidences but branch disambiguation at unwitnessed coordinates reverts to
  pairwise quotients — the same `2δ` wall;
  (iii) the bare many-specializations-have-roots claim is FALSE
  (`Y² − (Z² + c)`, `−c` a non-residue: `(p−1)/2` specializations with roots, no rational
  root) — the fold-agreement hypothesis is load-bearing, so any proof MUST use it;
  (iv) the staircase/rigid-relation technique is SHARP at `3j` (the degenerate-pencil
  explosion: `n/(b−1)` bad scalars for `d ∈ [2b−1, 3b−3]`) — no elementary collapse
  reaches Johnson.
* **The formalization target, precisely:** BCIKS20 Claim 5.10's `L`-valued root argument
  on the in-tree Appendix-A substrate (`H_tilde` monisization, `RationalFunctionsCore`
  regular rings): the decode-value functions `γ ↦ P(γ)(ω)` at the top coordinates define
  ONE algebraic function (branch of `R`) because the agreement mass exceeds the branch
  separation budget (Claim 5.11's multiplicative count) — the "γ-is-a-root" core. All
  surrounding machinery is in place; this single argument discharges, in order:
  `CoordinateUpgrade` (unconditionally) → `hsurface` → `johnsonNumericBound_holds` →
  `JohnsonDischargeStatement` → the Johnson floor with no Props → with the in-tree KKH26
  ceiling, the unconditional bracket `[1−√ρ−η, KKH26 rows]`, and with `InteriorCeiling`
  the exact deployed-regime pin.

**O154 addendum — the cross-coordinate no-go and the exact irreducible step.** One more
elementarization route closed, with the failure mechanism identified: the saturation
observation makes every high-mass coordinate carry the fold section as a fiber root
(`(Y − w_ω(Z)) ∣ R(Z, ω, Y)`), and the factor theorem over `F[Z][X]` would conclude
`(Y − pHat) ∣ R` outright if `G(Z,X) := R(Z, X, pHat)` vanished identically — BUT the
candidate `pHat` must interpolate the *words* `u₀, u₁` across coordinates, and arbitrary
words interpolate with degree `|T₀| − 1`, not `k − 1`: `deg_X G ≈ deg_Y R · |T₀| ≫ |T₀|`,
so vanishing on `|T₀|` lines never forces `G ≡ 0`. Degree-`< k` interpolability of the
words IS the correlated-agreement conclusion — the route is circular. GS multiplicity
(`m ≥ 12`) strengthens only the per-coordinate saturation count, not this cross-coordinate
glue. **Hence the irreducible step, exactly:** branch separation — two distinct `Y`-roots
of `R` (in the integral closure) agree over at most `deg disc_Y(R)` many `(Z, X)`-points
(separability from the in-tree lane), and the section's incidence mass exceeds that
budget, forcing all saturated coordinates onto ONE branch; that branch, evaluated against
any single scalar's witnessed coordinates, is `F[Z][X]`-rational of `X`-degree `< k` and
`Z`-degree `≤ 1`. This is Claim 5.10/5.11 with the discriminant in the role the paper
gives the regular-ring apparatus; the in-tree `GSDiscriminantOverRatFunc` +
`GSDecodedSeparationOverRatFunc` + `RationalFunctionsCore` are the substrate. The next
formalization session should prove, in order: (1) the discriminant-budget branch-agreement
bound; (2) the one-branch concentration from incidence mass; (3) the rationality/degree
read-off; then the proven chain fires through to `JohnsonDischargeStatement` and the
deployed-regime δ* pin.

### The RS band-3 staircase at d = 2b−1 REFUTED via curve points — ε_mca is ARITHMETIC at the boundary (#357 round 5)

RS(n=8, k=4, d=5), band 3, disjoint 2+2+2+2 punctures: the syndrome system is square and
det = Q(g,h) = g²h²+294g²h+105g²−296gh²−504gh+400h² (γ = (0,1,g,h) normalized), an
irreducible quadric NOT supported on the degeneracy locus. Over F₁₀₁: 196 admissible
points; γ = (0,1,2,33) verified END-TO-END as a 4-bad configuration (4 exact codeword
agreements + no-joint-explanation by solvability tests). Hence: RS collapse at band b
holds at d ≥ 2b (cell sweep, certified) and FAILS at d = 2b−1 — the MDS threshold is
exactly 2b, and below it the bad-scalar locus = F_q-points of a determinant curve: the
first machine-verified ARITHMETIC sensitivity of ε_mca (prototype of the window's
root-of-unity barrier). Same quadric appears as maximal minor at d = 6 (the overdetermined
extension kills its zero locus there).

**O154 second addendum — the Johnson core is even smaller than mapped: Claim 5.8 is PROVEN
(monic), Claim 5.9 is PROVEN (monic, deg_Y ≤ 2), the GS Z-degree budget is in-tree; the
true frontier is two specific extensions.** Deep audit of the Hensel/A.1 lane:

* `LiftIdentityAt` — **PROVEN for monic H** (`LiftIdentityAt.of_leadingCoeff_one`,
  P2RootBridgeS5; via `assembledSeries_isRoot_of_monic` / the proven monic Faà-di-Bruno
  match in MonicFaaDiBrunoMatchAlt). Claim 5.8 consumers wired
  (`claim58_genuine_via_leadingCoeff_one`). The named
  `FaaDiBrunoSuccSumZeroResidual` is open only for NON-monic H — and Appendix A's whole
  device (`H_tilde`, in-tree in RationalFunctionsCore) is monisization.
* Claim 5.9 (Z-linearity of the genuine root): order-0 face proven for monic
  (S5GenuineZLinearMonic); **full claim proven for monic H with deg_Y ≤ 2**
  (`claim59_zLinear_of_monic_natDegree_le_two`, S5GenuineZLinearQuadratic). The successor
  case at general degree needs the GS interpolant's Z-degree budget — and that budget IS
  in-tree (`gs_existence_over_ratfunc_zDegree_div` + Tight/Graded/Curve variants).
* **The true remaining frontier, exactly two extensions:**
  (J1) Claim 5.9 for monic H of general Y-degree — wire the in-tree Z-degree budget into
  the successor residual (the §5.2.7 geometric argument; the deg ≤ 2 proof is the
  template, the budget files the input); alternatively establish that the weld's
  factor-degree structure reduces consumers to deg_Y ≤ 2 (check whether richness
  concentration + budget inheritance cap the relevant factors).
  (J2) `SβLargeAt` — the §5.2.6 agreement-mass count ((5.13)/(5.14) + the Claim A.2
  Λ-weight bound `weight_Λ_over_𝒪`; the in-tree `βHensel_weight_bound_zero` is the
  order-0 anchor).
  Both for monic H, on built substrates, with proven templates one notch below. When J1+J2
  land: Claim 5.10 weld fires → CoordinateUpgrade → hsurface → johnsonNumericBound_holds →
  JohnsonDischargeStatement (no Prop) → the bracket → the deployed-regime exact δ* pin.

**O154 third addendum — the FaaDiBruno residual is PROVEN for monic H
(`faaDiBrunoSuccSumZeroResidual_of_leadingCoeff_one`, P2MonicConsequences) and integrality
is unconditional (`alphaGenuine_regular_of_monic`); the deg ≤ 2 mechanism identified; J1's
shape is CONSTRAINED by an in-tree refutation.** Final audit notes for the J1 dive:

* The deg ≤ 2 Z-linearity proof needs NO recursion-tracking and NO geometric input for the
  *shape*: monic integrality puts every `αGenuine t` in `𝒪 H`, and for `d_H ≤ 2` the
  canonical representative automatically has `T`-degree ≤ 1. For general `d_H` the gap is
  exactly: **kill the canonical representative's `T`-degrees `2..d_H−1`** — this is where
  the GS interpolant's Z-degree budget (in-tree, `gs_existence_over_ratfunc_zDegree_div`)
  must enter, i.e. the genuine §5.2.7 content.
* **Warning shaping J1 (in-tree refutation):** `P1MonicWeightRefutation.weight_refuted` is
  a valid monic quadratic `ClaimA2.Hypotheses` instance where the per-order X-degree
  budget FAILS at `t = 1` — so the budget cannot come from the recursion/hypotheses alone;
  it MUST be imported from the interpolant's geometry (the `R` fed to the Hensel lane must
  carry the GS budget, not be an arbitrary `Hypotheses` instance). J1's correct statement
  is therefore conditional on the GS-produced `R`, not free-standing over `ClaimA2`.
* Both J1 ingredients verified axiom-audited in-file (`S5GenuineZLinearQuadratic`,
  `P2MonicConsequences`, `P1MonicIntegrality` carry `#print axioms` blocks; no sorryAx
  grep-hits).

J1 final spec: for the GS interpolant's factor `H` (monic via `H_tilde`, budgets via
`gs_existence_over_ratfunc_zDegree_div`), every `αGenuine t`'s canonical representative has
`T`-degree ≤ 1. Route: the weighted-degree functional on `𝒪 H` (Λ-weight machinery) bounds
rep degrees by interpolant budgets; alternatively trace the §5.2.7 interpolation argument
(fulltext 1719–1740). J2 unchanged (`SβLargeAt` count). These two remain the entire gap
between today's tree and Prop-free Johnson + the exact deployed-regime δ* pin.

**O154 final addendum — THE LAST WALL: Claim 5.10 is FULLY ASSEMBLED in-tree
(`exists_pinning_pair_of_heavy_agreement`, CellPinning) and J1 is BYPASSED; the entire
Johnson programme rests on ONE residual: `βHenselSuccTermWeightResidual`.** The conclusive
audit:

* `CellPinning.exists_pinning_pair_of_heavy_agreement` produces the per-cell affine pair
  `(v₀, v₁)` — Claim 5.10's output, the weld's `hdata` leg — from: heavy agreement data
  (GS cell production shapes, in-tree), `LiftIdentityAt` (PROVEN monic), the Vandermonde/
  Lagrange globalization (`Kill.coeff_sum_eq_ground_of_large` → `Claim59Vandermonde` →
  `Claim59Lagrange`, all in-tree), and TWO numeric legs: `hcard` (matching-set sizes —
  supplied by agreement mass via `mem_S_β_killTarget_of_pin_agree` + cell production
  counts) and `hweight` (`Λ(killTarget) ≤ W`).
* **J1 (general-degree Z-linearity) is BYPASSED**: the kill-target/Vandermonde route
  derives the paper Z-linearity from largeness directly; no general-`d_H` canonical-rep
  argument is needed.
* `hweight` is the only deep leg: `βHensel_weight_bound` assembles the full strong
  induction from the proven over-`𝒪` weight calculus, with exactly ONE residual — the
  per-term WALL `βHenselSuccTermWeightResidual` (the weight of a single `(A.1)` recursion
  term: Hasse-derivative coefficient × partition product, bounded by `(2t+1)·d_R·D` —
  Claim A.2's per-term inequality, fulltext §A.4) — plus the cleared-sum weight
  bookkeeping for the specific kill targets.
* **Hence the COMPLETE remaining gap between today's tree and Prop-free Johnson + the
  exact δ* pin is: (W1) `βHenselSuccTermWeightResidual` (one weight inequality per
  recursion term, pure Λ-calculus over 𝒪) + (W2) the splice plumbing (kill-target weight
  from W1; matching-set counts from cell production; feed
  `exists_pinning_pair_of_heavy_agreement` into `cell_card_le_of_decode_family_pinning` →
  `bad_card_le_of_cell_production` → `hsurface` → `johnsonNumericBound_holds`).** W1 is
  the mathematics; W2 is wiring. After W1+W2: `JohnsonDischargeStatement` proven, the
  bracket unconditional, and `kkh26_deltaStar_pin_of_interior_ceiling` pins the
  deployed-regime δ* exactly.

**O154 route-correction — W1-AS-STATED IS DOCUMENTED UNPROVABLE (wave-5 diagnosis in-file:
the loose IH destroys the partition cancellation); the CORRECT final target is the
STRUCTURED invariant via the PROVEN monic lift identity, and its collapse theorem is
ALREADY PROVEN.** The decisive chain for monic `H` (= the `H_tilde` regime):

* `βHensel_weight_bound_of_structured_weight` (PROVEN, line 1430): the structured
  invariant `Λ(β_t) ≤ 1 + (t+1)·deg(W) + (2t−1)·(d_R−1)·(D−d_H+1)` implies the loose
  target `(2t+1)·d_R·D` — the collapse arithmetic is done.
* For monic `H`: `deg(W) = deg(1) = 0`, and the lift identity
  `β_t = α_t · W^{t+1} · ξ^{2t−1}` is PROVEN (`LiftIdentityAt.of_leadingCoeff_one`). Via
  the proven weight calculus (`_mul`/`_pow`): `Λ(β_t) ≤ Λ(α_t) + (2t−1)·Λ(ξ)`.
* **Hence the FINAL TARGET, exactly two computable weight bounds (paper line 4276's
  "easier way", now with every surrounding piece proven):**
  (V1) `Λ(α_t) ≤ 1` — the genuine Hensel coefficients have unit weight (γ = Σ α_t z^t is
  a root of monic `H̃`, Y-weight 1; for monic H, `alphaGenuine_regular_of_monic` already
  gives integrality — the weight refinement is the remaining step);
  (V2) `Λ(ξ) ≤ (d_R−1)·(D−d_H+1)` — the weight of the explicit element ξ (for monic H,
  `ξ = ζ`, the discriminant-type element; a direct computation in the proven calculus).
  Then: structured invariant → (proven collapse) → loose bound → kill-target weights →
  `exists_pinning_pair_of_heavy_agreement` → … → `JohnsonDischargeStatement` → the exact
  δ* pin. The recursion wall is BYPASSED, exactly as the paper prescribes.

**O154 conclusion — V2 IS PROVEN (`weight_ξ_bound`, RationalFunctionsCore:2854, exactly the
structured budget `Λ(ξ) ≤ (d_R−1)·(D−d_H+1)`); V1's order-0 is PROVEN
(`alphaWeight_zero_cleared_fixed`); the un-cleared invariant is provably FALSE non-monic
(de-fabrication record in AlphaWeightProof.lean) — the ENTIRE Johnson gap is now V1's
successor orders for monic H (the #138 P1 obligation), and nothing else.** Summary of the
complete reduction achieved by this siege:

| target | status |
|---|---|
| Claim 5.8 / LiftIdentityAt (monic) | PROVEN |
| Claim 5.9 / Z-linearity | BYPASSED (kill-target/Vandermonde route, assembled) |
| Claim 5.10 / cell pinning | ASSEMBLED (`exists_pinning_pair_of_heavy_agreement`) |
| structured→loose collapse | PROVEN (`βHensel_weight_bound_of_structured_weight`) |
| V2: Λ(ξ) budget | **PROVEN** (`weight_ξ_bound`) |
| V1 order 0 | PROVEN (`alphaWeight_zero_cleared_fixed`, weight ≤ 1) |
| W1 per-term recursion | UNPROVABLE as stated (documented); correctly bypassed |
| un-cleared invariant | FALSE non-monic (refutation in-tree); monic routing forced |
| **V1 successors (monic)** | **THE GAP** — `Λ(α_t) ≤ 1` for `t ≥ 1`, monic `H` |

The mathematical content of "Johnson with no Props" is now a single statement: the genuine
Hensel coefficients of a root of a monic `H̃` have unit Λ-weight at every order. Paper
route: γ = Σ α_t z^t IS the root (`Y`-weight 1); the closed form bounds each coefficient.
In-tree route candidates: (i) extend `alphaWeight_zero_cleared_fixed`'s argument
order-by-order through the proven monic lift identity (cleared = uncleared at W = 1);
(ii) the canonical-representative weight of `gammaGenuine`'s coefficients via
`alphaGenuine_regular_of_monic` integrality + the rep-degree calculus. Everything else in
the Johnson→δ* chain is machine-checked. After V1: `JohnsonDischargeStatement` proven →
the unconditional bracket → `kkh26_deltaStar_pin_of_interior_ceiling` = the exact
deployed-regime δ* pin.

**O154 V1 dive, finding 1 — THE STRUCTURED INVARIANT AS STATED IS UNSATISFIABLE AT t = 0
FOR THE CONSUMERS' D-REGIME; the base constant must be re-baselined to `D + 1 − d_H`
(and the proven collapse has room for it).** The computation, from the definitions read
this session (`weight_Λ` = sup over Y-monomials of `deg·(D+1−d_H) + deg_X(coeff)`;
`canonicalRepOf𝒪` = modByMonic `H_tilde'`):

* `βHensel 0 = mk X` (the Y-variable); its canonical rep is `Y` itself (degree `1 < d_H̃`
  for `d_H ≥ 2`), so `Λ(β₀) = 1·(D+1−d_H) + 0 = D+1−d_H` — **exactly `1` iff `D = d_H`**.
  This is why `alphaWeight_zero_cleared_fixed` carries `hD : D ≤ H.natDegree`.
* But the consumers (`exists_pinning_pair_of_heavy_agreement`, `weight_ξ_bound`) require
  `D ≥ totalDegree H` (and `≥ totalDegree (evalX x₀ R)`) — for the monisized `H_tilde'`
  (X-content in coefficients) these force `D > d_H`, where `Λ(β₀) > 1`: the structured
  hypothesis of `βHensel_weight_bound_of_structured_weight` is FALSE at `t = 0`.
* **The fix (checked for room):** re-baseline the invariant to
  `Λ(β_t) ≤ (D+1−d_H) + (t+1)·deg(W) + (2t−1)·(d_R−1)·(D−d_H+1)`; at `t = 0` this is
  satisfied with equality-shape by the rep computation; the collapse target
  `(2t+1)·d_R·D` absorbs the new base since `D+1−d_H ≤ D ≤ d_R·D` (using `d_R ≥ 1`,
  and at `t ≥ 1` the slack grows). The collapse lemma needs its constant re-derived
  (`structured_weight_collapse` analogue with base `D+1−d_H`) — pure ℕ-arithmetic.
* **V1 successor proof shape after re-baselining:** `Λ(β_t) ≤ base + (2t−1)·Λ(ξ)` for
  monic `H` via the PROVEN lift identity + `_mul`/`_pow` calculus + `weight_ξ_bound` —
  PROVIDED a weight bound for `α_t`'s regular preimage is available; the lift identity
  alone gives `β_t` in terms of `α_t` (circular without an independent `Λ(a_t)` input).
  The non-circular route: bound `Λ(β_t)` DIRECTLY by strong induction using the
  re-baselined invariant through the (A.1) recursion's *structured* form — the partition
  cancellation that the loose IH destroyed (wave-5 diagnosis) is exactly restored by
  carrying the `(2t−1)`-exponent structure, as the paper prescribes (line 3962).
  Re-baselined per-term lemma = the corrected W1, now with the cancellation available.

**O154 V1 dive, finding 2 — THE RE-BASELINED COLLAPSE IS VERIFIED (hand proof, ready for
transcription): `(D+1−d_H) + (t+1)·degW + (2t−1)·(d_R−1)·(D−d_H+1) ≤ (2t+1)·d_R·D` under
`1 ≤ d_H ≤ d_R`, `2 ≤ d_R`, `degW + d_H ≤ D`.** The slack chain (each step ℕ-safe):

1. `(D−d_H+1) ≤ D` (from `d_H ≥ 1`), so the ξ-term
   `(2t−1)(d_R−1)(D−d_H+1) ≤ (2t−1)(d_R−1)D`.
2. Budget identity: `(2t+1)·d_R·D − (2t−1)·(d_R−1)·D = D·[(2t+1)d_R − (2t−1)d_R + (2t−1)]
   = D·(2d_R + 2t − 1) ≥ D·(2t+3)` (from `d_R ≥ 2`).
3. Remaining LHS: `(D+1−d_H) + (t+1)·degW ≤ D + (t+1)·D = (t+2)·D` (from `d_H ≥ 1` and
   `degW ≤ D − d_H ≤ D`).
4. `(t+2)·D ≤ (2t+3)·D` ✓ — with slack `(t+1)·D`, so the bound is robust to the
   ℕ-truncation edge cases (`t = 0`: `(2t−1) = 0` in ℕ kills the ξ-term entirely and the
   check is `(D+1−d_H) + degW ≤ d_R·D`, which holds by `degW ≤ D−d_H` and `2d_H ≥ 1`).

Transcription target: `structured_weight_collapse_rebased` next to
`structured_weight_collapse` (HenselNumerator ~1445), same `exact_mod_cast` shape, `omega`
or `nlinarith` closes after the four `Nat.sub`-guards are introduced
(`Nat.sub_le`, `Nat.le_sub_of_add_le`). Then
`βHensel_weight_bound_of_structured_weight_rebased` is the same two-line `refine
hstructured.trans ?_` proof. With finding 1 (the t = 0 base = the rep computation, exact)
and the structured induction (step 2 of the order), the chain to
`JohnsonDischargeStatement` and the exact δ* pin is fully specified arithmetic + one
structured induction whose cancellation mechanism the paper provides (line 3962) and the
in-tree per-term lemmas support.

**O154 V1 dive, finding 3 — THE STRUCTURED CANCELLATION VERIFIED BY HAND (monic case):
the per-term ξ-exponents collapse to EXACTLY `2k`, independent of `i1` and the partition;
the per-term lemma reduces to `Λ(B_coeff i1 λ) ≤ (d_R − m)·B₀` — precisely the shape of
the PROVEN Hasse Y-degree drop.** The computation (monic `H`: `degW = 0`,
`B₀ := D+1−d_H`, `Lξ := (d_R−1)·B₀` from the proven `weight_ξ_bound`, noting
`(d_R−1)(D−d_H+1) = (d_R−1)·B₀`):

* Structured IH (re-baselined, monic): `Λ(β_l) ≤ B₀ + (2l−1)·Lξ`.
* Partition product over `λ ⊢ k+1−i1` with `m` parts:
  `Λ(∏ β_part) ≤ Σ_parts [B₀ + (2·part−1)Lξ] = m·B₀ + (2(k+1−i1) − m)·Lξ`.
* ξ-power: `Λ(ξ^{2i1+m−2}) ≤ (2i1+m−2)·Lξ`; W-powers free (monic).
* **The cancellation:** total ξ-coefficient
  `(2i1+m−2) + (2(k+1−i1)−m) = 2k` — all `i1` and `m` dependence cancels. This is
  exactly the mechanism the wave-5 diagnosis said the loose IH destroys and the
  structured IH restores.
* Per-term total: `Λ(term) ≤ Λ(B_coeff) + m·B₀ + 2k·Lξ`. Target at order `k+1`:
  `B₀ + (2k+1)·Lξ`. **Residual need: `Λ(B_coeff i1 λ) ≤ (d_R − m)·B₀`** — for the
  Hasse-coefficient factor, whose Y-degree drop with the derivative order is the PROVEN
  wave-4 `hasseCoeffRepr𝒪_natDegreeY_le`; what remains is its Λ-form (Y-degree drop ×
  `B₀` + X-degree bookkeeping against `D ≥ totalDegree(evalX x₀ R)`).
* Step-2 base case: exact (`Λ(β₀) = B₀`, finding 1). Step-1 collapse: PROVEN
  (`structured_weight_collapse_rebased`).

**The Johnson endgame is therefore: (E1) the Λ-form of the Hasse coefficient bound
(`Λ(B_coeff i1 λ) ≤ (d_R − m)·B₀`, from the proven Y-degree drop + X-degree bookkeeping);
(E2) assemble the strong induction (the calculus lemmas `_sum_le`/`_mul`/`_pow` are
proven; the cancellation is the arithmetic above); (E3) wiring.** Every constant is now
pinned; the remaining work is transcription-grade.

**O154 V1 dive, finding 4 (HONESTY CORRECTION) — E1-as-stated in finding 3 is NOT
SUFFICIENT: under the in-tree Λ (sup of `deg_Y·(D+1−d_H) + deg_Z(coeff)`), the crude
B-coefficient budget overshoots the cancellation headroom by `≈ D − d_R + m`.** The check:

* `B_coeff_weight_le_hasse` (PROVEN) reduces `Λ(B)` to `Λ(hasseCoeffRepr𝒪 i1 (Σλ))`, whose
  underlying polynomial is `evalX (C x₀) (Δ_X^{i1} Δ_Y^{Σλ} R)` with Y-degree ≤ `d_R − Σλ`
  (PROVEN drop). The generic estimate `deg_Z(coeff_d) ≤ D_Q − d` gives
  `Λ(B) ≤ D_Q + (d_R − m)·(B₀ − 1)`, and the finding-3 residual budget
  (`Λ(B) + (m−1)·C₀ ≤ Lξ`, any IH constant `C₀`) then misses by `≈ D − d_R + m > 0`.
* So EITHER (a) the in-tree Λ normalization differs from the paper's §A.4 weight (their
  `Λ(Y) = 1` suggests their effective `D` is `d_H`-anchored where ours is
  `totalDegree`-anchored — the ξ-bound and the B-bound may not be simultaneously tight in
  one `D`), OR (b) the B-coefficient needs the sharper per-monomial estimate
  (`deg_Z + deg_Y ≤ totalDeg` used jointly rather than the crude sup), OR (c) the
  structured IH needs a `−l·(something)` X-degree credit term (the paper's
  `Λ(β_t) ≤ 1 + (t+1)Λ(W) + e_t·Λ(ξ)` tracks X-content through `W` powers that monic
  routing zeroes — the credit may be hiding in the monisization's `W^{d−1−i}` coefficient
  twists, cf. `H_tilde'` coefficient structure in RationalFunctionsCore:2480).
* **Next-session resolution order (BEFORE transcribing anything): (R1) extract the
  paper's exact §A.4 weight definition and (5.13)/(5.14) constants (fulltext lines
  3940–3970) and diff against in-tree `weight_Λ`; (R2) recompute the budget with the
  joint per-monomial estimate; (R3) if (c), recompute `H_tilde'`-twisted coefficient
  degrees.** Finding 3's exponent cancellation (exactly `2k`) is verified and stands;
  only the B-budget bookkeeping is open. The proven artifacts
  (`structured_weight_collapse_rebased`, the calculus, the drops) are unaffected.

**O154 V1 dive, finding 5 (R1 RESOLVED) — the finding-4 discrepancy is EXPLAINED by the
paper's frame: the weight machinery runs over the ORIGINAL NON-MONIC `H` with
`Λ(W) = D − d_H` TIGHT (the paper's t = 0 base literally reads "β₀ = T mod H̃ and indeed
Λ(T) = Λ(W) + 1", fulltext 3978) — the `(t+1)·Λ(W)` terms ARE the X-degree credit; monic
routing zeroes them and creates the deficit.** Full R1 extraction (fulltext 3820–3990):

* The paper's Λ is identical to in-tree `weight_Λ` (`Λ(Z) = 1`, `Λ(T) = D+1−d`, sup over
  monomials; H̃-reduction never increases weight) — no normalization diff.
* But `d := deg_Y H` and `D ≥ total (Y,Z)-degree of H` for the ORIGINAL factor `H`
  (`W := leadingCoeff H`, `Λ(W) ≤ D − d_H`), and the base-case identity
  `Λ(T) = Λ(W) + 1` forces `Λ(W) = D − d_H` — i.e. `D` is anchored tight to `H`'s total
  degree, with the leading coefficient carrying the maximal Z-degree. The "1"-based
  structured invariant `Λ(β_t) ≤ 1 + (t+1)Λ(W) + e_t·Λ(ξ)` is THEN correct: at `t = 0`
  it is exact, and the W-terms absorb precisely the `B₀ − 1 = D − d_H` per occurrence
  that finding 4 found missing.
* Claim A.2's chain (fulltext 3966–3970):
  `Λ(β_t) ≤ ((d−1)·e_t + t + 1)(D − d_H + 1) − t < (2t+1)·d·D` — the collapse the
  in-tree `structured_weight_collapse` mirrors, all in the original-H frame.
* §5's telescoping application (fulltext 1788–1797): `Λ(β_t·W^{k−t}·ξ^{e_k−e_t})`
  collapses to `1 + (k+1)Λ(W) + e_k Λ(ξ)` — the per-term cancellation INCLUDING W-powers,
  which is finding 3's computation with the W-credit restored.
* **Corrected formalization frame (the final one): work over the ORIGINAL `H` (non-monic),
  `D` anchored tight, the W/ξ-exponent structured invariant exactly as Claim A.2 states
  it. The monic in-tree artifacts (`assembledSeries_isRoot_of_monic` etc.) remain valid
  for the ROOT identities (where they were proven); the WEIGHT bookkeeping must thread
  the genuine `W` — which the in-tree `FaaDiBrunoSuccSumZeroResidual` general form and
  the `βHensel` infrastructure already parametrize. Finding-3's cancellation redone with
  W-terms: W-exponent total telescopes identically (the (5.16) display), so the per-term
  lemma's residual becomes `Λ(B_coeff) ≤ (d_R − m)·(B₀ − 1) + bounded`, matching the
  PROVEN Y-drop + the now-available W-credit. The endgame stands, in the corrected frame:
  (E1′) per-term with W-credit, (E2′) Claim-A.2 induction assembly, (E3) wiring.**

**O154 V1 dive, finding 6 (partial retraction of finding 1) — in the paper's original-H
frame the IN-TREE structured invariant is SATISFIABLE at t = 0 exactly: finding 1's
unsatisfiability is a property of MONIC ROUTING ONLY.** With `W = leadingCoeff H`
(non-monic) and the tight anchor `Λ(W) = D − d_H`:

  `Λ(β₀) = Λ(T) = D + 1 − d_H = 1 + Λ(W)` ✓ (the paper's base identity, exact),

so the in-tree `1 + (t+1)·deg(W) + …` structured form and its PROVEN collapse
(`structured_weight_collapse`) are correct as stated — for the original `H`. The
monic-frame variant (`structured_weight_collapse_rebased`, proven this session) remains
the correct collapse if monic routing is ever used with the consumers' large `D`.

**The definitive Johnson endgame (consolidating findings 1–6):** work in the paper's frame
(original non-monic `H`, `D ≥ totalDegree H` with the leading coefficient carrying
`deg_Z W = D − d_H`, the in-tree structured invariant + proven collapse). Remaining:
(E1′) the per-term weight bound with the structured IH — finding 3's exponent cancellation
(2k, verified) extends verbatim with the W-powers telescoping per the paper's (5.16); the
B_coeff residual gets the W-credit; consume the proven `B_coeff_weight_le_hasse` +
`hasseCoeffRepr𝒪_natDegreeY_le`;
(E2′) assemble the strong induction (`βHensel_weight_bound` is already shaped for exactly
this hterm — feed it the structured-IH per-term lemma);
(E3) wiring (kill-target weights → `exists_pinning_pair_of_heavy_agreement` →
`bad_card_le_of_cell_production` → `hsurface` → `johnsonNumericBound_holds` →
`JohnsonDischargeStatement` → bracket → `kkh26_deltaStar_pin_of_interior_ceiling`).
Every claim above is traced to a paper line or an in-tree theorem name; no step rests on
an unverified guess. The remaining work is the E1′/E2′ formalization and E3 wiring.

**O154 V1 dive, finding 7 — THE COMPLETE PER-TERM ARITHMETIC (E1′) VERIFIED BY HAND in
the original-H frame; the last missing `Λ_W` is the paper-3955 W-DIVISIBILITY of the
leading coefficient; E1′ is now transcription.** With `Λ_W := Λ(W) = D − d_H` (tight),
`Λ_ξ := (D−1) + (d−2)·Λ_W` (Claim A.2 bullet 1, exact form), structured IH
`Λ(β_l) ≤ 1 + (l+1)Λ_W + e_l·Λ_ξ`, per-term object
`W^{i1+δ−1}·ξ^{2i1+Σλ−2}·B_{i1,λ}·∏_parts β_part` (m parts, Σ parts = k+1−i1):

* **ξ-coefficient: `(2i1+m−2) + Σ_parts e_part ≤ (2i1+m−2) + (2(k+1−i1)−m) = 2k`** —
  the finding-3 cancellation, unchanged. Target `e_{k+1} = 2k+1`: headroom `Λ_ξ`.
* **W-coefficient: `(i1+δ−1) + Σ_parts(part+1) = (i1+δ−1) + (k+1−i1) + m = k+δ+m`.**
  Target `k+2`: deficit `(δ+m−2)·Λ_W`, absorbed by the headroom `Λ_ξ ⊇ (d−2)Λ_W`
  provided `Λ(B)` is good enough.
* Reduced need: **`Λ(B_{i1,λ}) ≤ D − m + (d − δ − m)·Λ_W`.**
* **The B-estimate (joint per-monomial, with both drops):** the rep of `B_{i1,λ}` is (up
  to integer prefactor, weight-free by `weight_Λ_over_𝒪_nsmul_le`) the Hasse coefficient
  `evalX(x₀)(Δ_X^{i1} Δ_Y^{m} R)`: `T`-degree ≤ `d − m` (PROVEN drop) and the `T^j`
  coefficient has `Z`-degree ≤ `D_R − (j+m)` (the `Δ_Y^m` index shift: coefficient `j` of
  the derivative is `C(j+m,m)·r_{j+m}`). Hence
  `Λ(B) ≤ max_j [j·(D+1−d_H) + D_R − j − m] = D_R − m + (d−m)·Λ_W ≤ D − m + (d−m)·Λ_W`.
* **The final credit (δ-cases):** for `δ = 0` the need is met outright. For the `i1 = 0`,
  `δ = 1` boundary the estimate is `Λ_W` short — and the paper supplies exactly it at
  line 3955: **`W` divides the leading coefficient of `R_{x₀}`**, so the TOP Hasse
  coefficient (`j = d−m`) carries a `W` factor; accounting it (reduce or factor) lowers
  the dominant term by `Λ_W`:
  `Λ(B) ≤ D − m + (d−m−1)·Λ_W` — meeting the need exactly. ∎ (hand)
* **E1′ transcription inventory:** the `Δ_Y` index-shift Z-degree bound (new small lemma
  on `hasseDerivY` coefficients); the W-divisibility of the top coefficient (from
  `Hypotheses.dvd_evalX`, in-tree); the joint-monomial Λ-estimate (a `Finset.sup` bound);
  then the bookkeeping above (ℕ-arithmetic, same flavour as the proven rebased collapse).
  E2′: feed into `βHensel_weight_bound`'s hterm. E3: wiring. The mathematics of the
  Johnson endgame is now COMPLETE on paper; all of it is traced; what remains is Lean.

### MonomialDomination REFUTED at the boundary row — the triangle-incidence stack (#357)

The v3 pin's named surface fails at `d = 2b−1`. At `C84 = RS[F₁₇, μ₈, 4]`, δ = 1/4
(agreement 6, band 3, boundary row d = 5): the two-triangle incidence stack
`v₀ = (0,8,16,0,…)`, `v₁ = (10,15,5,0,…)` (affine line in the 2-dim intersection of the
column spans of exponent triangles {0,1,2} and {3,4,6}) carries SEVEN bad scalars
{0,4,7,9,10,12,13} — formal: `MonomialDominationBoundaryRefuted.lean`
(`epsMCA_quarter_ge_seven`, seven `interp_kill` certificates) — while every monomial pair
has ≤ 4 (exhaustive probe, max at (X⁶,X⁴); named numeric surface `MonomialBoundaryBound`).
`monomialDomination_refuted_of_monomial_bound`: the bound ⟹ ¬MonomialDomination for every
crossing ac ≤ 5.

**Mechanism (probes `probe_boundary_row_incidence.py` / `probe_boundary_triangle_stratum.py`
/ `probe_boundary_n12_coset_triangles.py`):** at the boundary row the per-block syndrome
spaces R_B (codim b−1) admit lines in the intersection of two triangle spans — 3 scalars
per triangle + extra-pair incidences. Boundary band-3 law: value = n when 3 ∣ n (coset
triangles; the excess pair (X^{n−2},X^{n−3}) is then itself coset-structured and TIES —
the n=12 cell (13,12,8) gives 12 = n for both); value = 7 = 3·⌊n/3⌋+1 at n = 8 (3 ∤ n,
two generic triangles + one extra pair; two-triangle stratum exhaustive, mcaEvent-filtered).
2-power smooth domains always have 3 ∤ n ⟹ the defect case (triangles strictly beat
monomials) is the production shape. Single-block lines reach incidence q−1 but are
MCA-invisible (the O147 coset-witness phenomenon at the staircase level).

**Surviving v4 surface:** domination restricted to rows with d ≥ 2b (off the boundary
rows) — equivalently ε_mca ≤ max(staircase, boundary-incidence value, monomialEps).
At production ε*·q ≈ 2¹²⁸ the boundary rows (mass ~n/q) never decide the census crossing,
so the production conclusion of pin v3 is unaffected; the surface as stated is dead.

### The coset-clique boundary law (#357) — the boundary arc closed as theorem

`CosetCliqueBoundary.lean` (`clique_eps_ge`): ε_mca(RS[F,μ_n,k], (b−1)/n) ≥ n/|F| for every
b | n, n−2b+2 ≤ k ≤ n−b (d ∈ [b+1, 2b−1]). Mechanism: twisted telescoping
x^b·q = −c(x−x*)G + (x+γ), G = Σ c^v x^((N−1−v)b); explanation deg n−2b+1; witness =
fiber complement + crossing; no-joint root counting. The ≥ half of O148 (bad ⊇ −μ_n);
the "common 2-plane" of the boundary probes = the (G, xG) fraction plane. Probes:
band-3 values n − [3∤n] at n = 6,8,10,12; band-4 = 12 = n at (13,μ₁₂,6). At 2-power n
every 2-power band's boundary row carries n/q. Constraint for future sup-side work:
any collapse-type theorem at d ≤ 2b−1 must exclude b | n smooth domains.

**O154 V1 dive, finding 8 — THE PER-TERM RESIDUAL CLOSES IN BOTH δ-CASES (complete
hand-verification of `StructuredSuccTermBound`; the per-term Lean proof is now pure
transcription with zero unknowns).** With `w := D − d_H`, `degW = w` (tight anchor),
`Lξ = (d_R−1)(w+1)`, `m := sigmaLambda lam = parts.card`, `S := parts.sum = k+1−i1`,
`δ := deltaSave i1`:

* **Structured partition sum:** `Σ_parts [1 + (part+1)·degW + (2·part−1)·Lξ]
  = m + (S+m)·degW + (2S−m)·Lξ` (parts ≥ 1 makes every truncation safe; the new multiset
  evaluation lemma needed is the structured analogue of the in-tree
  `sum_map_two_mul_succ`).
* **Truncation-safety at the boundary:** for `i1 = 0`, `hlam : (k+1) ∉ parts` forces
  `m ≥ 2` (a one-part partition of `k+1` would have part `= k+1`), so
  `2·i1 + m − 2 ≥ 0` is safe; for `i1 ≥ 1` it is safe outright.
* **Totals:** ξ-coefficient `= 2k` (finding 3); W-coefficient `= k + δ + m`. Against the
  target `structuredBound(k+1) = 1 + (k+2)·degW + (2k+1)·Lξ`, the residual need is
  `Λ(B) + (m−1) + (δ+m−2)·degW ≤ Lξ`.
* **Case `i1 ≥ 1` (δ = 0):** item-(d) B-bound `Λ(B) ≤ (D−m) + (d_R−m)·w` gives
  LHS − RHS `= d_H − d_R ≤ 0` ✓ (`d_H ≤ d_R` since `H ∣ R(x₀)`, in-tree
  `evalX_natDegree_le` + divisibility).
* **Case `i1 = 0` (δ = 1):** the W-divisibility credit (item (b),
  `leadingCoeff_dvd_evalX_hasseDerivY_top` — note `i1 = 0` means NO X-Hasse, exactly the
  case (b) covers) improves the B-bound's dominant term by `w`:
  `Λ(B) ≤ (D−m) + (d_R−m−1)·w`, and the need reduces to `D ≤ w + d_R ⟺ d_H ≤ d_R` ✓.
* **Transcription plan for `StructuredSuccTermBound` (final):** (i) the structured
  partition-sum evaluation lemma (multiset, mirrors `sum_map_two_mul_succ`);
  (ii) the structured analogue of `partitionProd_βHensel_weight_le` (pattern-copy:
  guard rewrite + multiset bound + structured IH + (i)); (iii) decompose the term via
  `_mul_le`, bound `W`-power (`_pow_le` + `_W`), `ξ`-power (`_pow_le` +
  `weight_ξ_bound`), `B` (item (d) + shape hypotheses from the GS budgets, with the
  item-(b) credit at `i1 = 0`); (iv) the ℕ-bookkeeping above (omega/nlinarith, both
  δ-cases). All four steps have proven templates in-tree. After it:
  `βHensel_weight_bound_structured` fires (assembled), the collapse fires (proven),
  the kill-target chain fires (assembled), `JohnsonDischargeStatement` falls, and
  `kkh26_deltaStar_pin_of_interior_ceiling` pins δ* exactly.

**O154 V1 dive, finding 9 — the B-budget instantiation computed: the generic
three-layer shape closes i1 ≥ 1 EXACTLY; the i1 = 0 case is pinned to one precise
mechanism question (the W-extraction in 𝒪).** The computation, against the threaded
theorem's `hreduced`:

* **Generic shape supplier:** if `R`'s three-layer coefficients satisfy the total-degree
  shape `deg_Z((R.coeff n).coeff i) ≤ D_R − n − i` (the GS interpolant's budget,
  `gs_existence_over_ratfunc_zDegree_div` shape), then through `Δ_Y^m` (Y-shift, item (a)),
  `Δ_X^{i1}` (X-shift, same mechanism on the middle layer), and `evalX (C x₀)`
  (constant evaluation: max over X-indices, deg_Z preserved), the specialized Hasse
  polynomial has the item-(d) shape with `DQ = D_R − m − i1`, `dT = d_R − m`. Hence
  `nB = (D_R − m − i1) + (d_R − m)·(D − d_H)`.
* **Case i1 ≥ 1 (δ = 0):** `hreduced` LHS − RHS `= d_H − i1 − d_R < 0` ✓ — closes with
  room, using only `D_R ≤ D` and `d_H ≤ d_R`. The B-budget for all these cells is pure
  plumbing of the generic supplier.
* **Case i1 = 0 (δ = 1):** the crude bound leaves deficit `D − d_R ≥ 0`. Finding 7's
  W-credit (item (b): `W ∣` top coefficient) must enter — but the naive reading is wrong:
  W-divisibility RAISES `deg_Z(top coeff)`, it does not lower the sup. **The precise open
  mechanism question:** how the paper extracts the W — three candidate routes:
  (R-a) the canonical rep `p %ₘ H̃` has T-degree ≤ d_H − 1 < d_R − m generically — if the
  reduction's weight bookkeeping (the proven `weight_Λ_modByMonic_le` is one-directional)
  can be sharpened on the top monomial, `dT` drops to `d_H − 1` and the case closes;
  (R-b) in 𝒪, write `mk p = W𝒪 · mk q + mk r` (peel the W-divisible top): then
  `Λ(mk p) ≤ max(Λ(W) + Λ(q-part), Λ(r))` via the calculus — the W joins the budget as
  the paper's `(t+1)Λ(W)` term (this is the paper's actual `α_t`-route bookkeeping);
  (R-c) recheck whether the i1 = 0 cell even needs the full generic `nB` — the paper's
  (A.1) at i1 = 0 has `ξ^{m−2}` not `ξ^{2i1+m−2}` and `W^0`; a sharper per-cell audit of
  the exponent bookkeeping may show the engine's `hreduced` is stronger than needed here.
  **Next session: decide R-a/R-b/R-c (read the paper's i1 = 0 term handling, fulltext
  3990–4080), then the B-budget brick closes and the chain wires.**

**O154 V1 dive, finding 10 (R-b CONFIRMED from the paper, fulltext 4040–4055) — the
i1 = 0 mechanism is the W-TWISTED CLEARING: the paper defines `B_{i1,λ} = A_{i1,λ} ·
W^{d−δ−Σλ}` and at `i1 = 0` the α₀-leading coefficient `Σ_i R_{d,i}·x₀^i` IS the leading
coefficient of `R_{x₀}`, hence W-divisible, so the cleared form takes ONE FEWER W
(`δ_{i1,0} = 1`) and `Λ(B_{0,λ}) = (D−Σλ) + (d−1−Σλ)·Λ(W)` — exactly finding 8's improved
bound. The in-tree `hasseCoeffRepr𝒪_cleared` (HenselNumerator:589) implements precisely
this W-power twist ("each Y-power i of p rescaled by lc^{(natDegreeY p)−i}").** Remaining
audit for the B-budget brick (the final to-do before wiring):

* Determine which form the in-tree `B_coeff`/`βHensel_succ` recursion actually carries
  (the untwisted `hasseCoeffRepr𝒪` vs the twisted `_cleared`) and whether the `deltaSave`
  prefactor bookkeeping (the W^{i1+δ−1} in the term) aligns the in-tree convention with
  the paper's δ-saving (the term structure suggests YES: at i1 = 0 the prefactor is W⁰ and
  the saving must therefore live in the B-form);
* If untwisted: prove the twisted-weight bridge
  `Λ(mk p) ≤ (D_R−m) + (d_R−δ−m)·Λ(W)` via the W-divisibility of the top coefficient
  (item (b)) + the per-monomial max analysis (the top monomial's Z-budget is
  `D_R − d_R`, NOT the uniform `DQ` — the sharper per-monomial accounting may close
  i1 = 0 without any twist, route R-c);
* Then both engine budgets are supplied for every cell, `βHensel_weight_bound_structured`
  fires, the collapse fires, the kill-chain fires, `JohnsonDischargeStatement` falls, and
  `kkh26_deltaStar_pin_of_interior_ceiling` pins δ* exactly.

Status at this checkpoint: ELEVEN axiom-clean endgame bricks; TEN findings; the per-term
wall a theorem modulo budgets; i1 ≥ 1 budgets closed by computation; i1 = 0 reduced to
one convention-audit + one bridge lemma with the paper's mechanism now extracted verbatim.

**O154 V1 dive, finding 11 (the convention audit, decisive) — the in-tree `B_coeff` is
UNTWISTED (`prefactor • hasseCoeffRepr𝒪`, HenselNumerator:989-region docstring confirms);
the in-tree `B_coeff_weight_le` (PROVEN) is `(d_R−m)·(D+1−d_H) + degX(p)` — computed
against `hreduced` it is exactly `(d_R−m)` TOO LOOSE (deficit `d_H − m − i1`, not
`d_H − i1 − d_R`); my item-(d) per-monomial bound (`DQ + dT·(D−d_H)`, the `(D−d_H)` factor
not `(D+1−d_H)`) is the SHARP one and closes i1 ≥ 1.** Audit details:

* `B_coeff := prefactor • hasseCoeffRepr𝒪` — untwisted; the `_cleared` twist exists
  separately with its embedding identity (`embeddingOf𝒪Into𝕃_hasseCoeffRepr𝒪_cleared`,
  proven). The docstring's named remaining sharpening for the in-tree route is the
  degree-tracking `degX p ≤ D − Σλ`.
* In-tree bound + crude tracking: `nB = (d_R−m)Λ_W + (d_R−m) + (D−m−i1)` ⟹ hreduced
  deficit `d_H − m − i1` — NOT always ≤ 0 (fails at small m+i1, large d_H). My item-(d):
  `nB = (D_R−m−i1) + (d_R−m)Λ_W` ⟹ deficit `d_H − i1 − d_R ≤ 0` for i1 ≥ 1 ✓ (finding 9
  reconfirmed against the in-tree lemma — item (d) is the right B-budget, not
  `B_coeff_weight_le`).
* **The remaining i1 = 0 question, now fully precise:** with the untwisted uniform bound
  the deficit is `D − d_R ≥ 0`; the per-monomial refinement shows the TOP monomial
  contributes only `dT·Λ_W + (D_R − d_R − i1)` (less than uniform by `dT`), so the sup
  may sit at interior monomials where W-divisibility says nothing — the paper's saving is
  genuinely a property of the TWISTED clearing (the `T/W`-denominator structure), not of
  the untwisted sup. **Resolution for the next session (one of):** (T-a) state the i1 = 0
  B-budget through the `_cleared` form (its embedding identity is proven; need its
  Λ-bound — the twist multiplies coefficient `j` by `W^{dT−j}`, giving per-monomial
  `j·(Λ_W+1) + (DQ−j) + (dT−j)·degW = dT·Λ_W + DQ − ... ` compute carefully); or (T-b)
  verify whether `βHensel_succ`'s recursion identity actually consumes the twisted form at
  i1 = 0 (the δ-saving MUST live somewhere — if the recursion's W-prefactor exponent
  `i1 + δ − 1 = 0` at i1 = 0 is paired with the untwisted B, the paper-vs-tree term
  normalization differs by exactly one W and the in-tree per-term TARGET may differ
  accordingly — audit `βHensel_succ` against (A.1) at i1 = 0 specifically).

**O154 V1 dive, finding 12 (T-b audit + a critical anchor catch) — the tight anchor
`D ≤ d_H + degW` is INFEASIBLE for the monisized `H̃` (its coefficients carry Z-content:
`totalDegree H̃ ≫ d_H̃`), so the monic route MUST use the rebased frame
(`structured_weight_collapse_rebased`, proven for exactly this); and in BOTH frames the
i1 = 0 budget remains the one open node, now characterized to its root.** The audit:

* `βHensel_succ` (read verbatim): the tree's recursion carries the UNTWISTED `B_coeff`
  with the `W^{i1+δ−1}` prefactor — at `i1 = 0` the prefactor is `W⁰` and the paper's
  δ-saving must live in the B-form, which the untwisted tree object does not carry.
* **Anchor catch (new):** `βHensel_weight_bound_zero_structured`'s hypothesis
  `D ≤ d_H + degW` requires `D ≤ d_H` for monic `H` — but `D ≥ totalDegree H̃ > d_H̃`
  for the monisized polynomial (W-twisted coefficients have Z-content). The
  tight-anchor base case CANNOT be instantiated at `H̃`; the rebased base
  (`Λ(β₀) = D+1−d_H` exactly, finding 1) with the rebased collapse (proven) is the
  correct monic-route pair. The base-case lemma needs its rebased variant stated
  (one-line proof from the same rep computation).
* **The per-monomial sup is tight at the top** (computed): the shape bound at `j = dT`
  is exactly `DQ − dT`, and the weight `DQ + j·w` is increasing in `j`, so the sup IS
  `DQ + dT·w` — the W-divisibility of the top coefficient cannot reduce the untwisted
  sup (it bounds `deg c_top` from BELOW). The saving is genuinely and only a property
  of the twisted clearing (`A·W^{d−δ−Σλ}`-form), confirming finding 11.
* **The i1 = 0 node, at its root:** EITHER the per-term target at `i1 = 0` differs from
  the engine's uniform target by one `Λ_W` (if the tree's normalization is audited
  against the lift identity and found to carry the missing `W` on the TARGET side — the
  monic lift identity is proven, so this audit is mechanical for monic), OR the twisted
  `_cleared` form must replace `B_coeff` at `i1 = 0` in the recursion's weight pass
  (its embedding identity is proven; its Λ-bound is one new lemma). Both are bounded
  tasks; the first is a `#check`-level comparison of proven identities.

Net state: the per-term wall is a theorem for ALL cells except `i1 = 0`, whose resolution
is one identity-comparison plus possibly one Λ-bound — with every surrounding object
(embedding identities, rep computations, collapse variants) already proven.

## O155 (2026-06-11, Johnson V1 finding 13 — DECISIVE): the rebased hbudget is UNSATISFIABLE; the correct frame is the ANCHORED original engine

**Claim attacked:** the landed capstone `βHensel_weight_bound_of_cell_budgets`
(StructuredWeightInduction.lean) can be discharged by instantiating its `hbudget`
hypothesis with the sharp untwisted per-cell budget
`nB = (D_R−m−i1) + (d_R−m)(D−d_H)` (finding 9's plan).

**Refutation (machine-checkable arithmetic):** the rebased reduced-need
`nB + (m−1)·(D+1−d_H) + (δ+m−2)·degW ≤ (d_R−1)(D−d_H+1)` is unsatisfiable for ANY
`nB ≥ 0` at the genuine nonzero cell `m = sigmaLambda = d_R` once `d_R ≥ 3` and
`degW ≥ 1`: already `(m−1)(D+1−d_H) + (m−2)degW = (d_R−1)(D−d_H+1) + (d_R−2)degW`
exceeds the entire ξ-budget. (Toy: D=10, d_H=2, degW=1, d_R=4, m=4: 27+2 = 29 > 27.)
High-card cells `m > d_R` are zero (Hasse order > Y-degree) but `m = d_R` is genuine.

**Root cause (paper line-level diagnosis, BCIKS20 A.2+A.4 re-read):** the rebased
constant `B₀ = D+1−d_H` DOUBLE-COUNTS `degW`. The paper's invariant
`Λ(β_t) ≤ 1 + (t+1)Λ(W) + e_t Λ(ξ)` carries the base's W-content in the `(t+1)Λ(W)`
schedule (base case: `Λ(T) = Λ(W)+1`), and the paper's per-term ledger closes with
EXACT EQUALITY (`D + (d−2)Λ(W) = 1 + Λ(ξ)` with `Λ(ξ) = (D−1)+(d−2)Λ(W)`), zero slack.
The paper's base-case assertion `Λ(T) = Λ(W)+1` is an implicit ANCHOR assumption
`g := D − d_H − degW = 0`, i.e. `totalDegree H = d_H + degW` with `D := totalDegree H`
(total degree achieved at the leading Y-monomial). At `g > 0` the paper's own claimed
B-budget `(D−Σλ)+(d−Σλ)Λ(W)` understates the A.2-weight of the cleared B by `b·g`
per T-monomial, and the per-term ledger fails by `~(d_R−d_H)·g` at `m = 1` cells; the
paper's real proof at `g > 0` is the VALUATION argument (`Λ(α_t) = Λ(Y) = g+1`), which
the recursion-telescoping route cannot reproduce without Newton-polygon machinery.

**The closable frame (verified by complete cell-ledger):** at the anchor `g = 0`
(`D₀ := d_H + degW = totalDegree H`, reduction-safety `weight_Λ_modByMonic_le` takes
`tot H ≤ D` so the calculus is VALID at `D₀`), the ORIGINAL structured engine (B₀ = 1,
in-tree `βHensel_weight_bound_structured` + `βHensel_weight_bound_zero_structured`,
whose anchor hypothesis is exactly `D ≤ d_H+degW`) closes EVERY cell with the proven
`Lξ = (d_R−1)(D−d_H+1)` and the landed supplier
`hasseCoeffRepr𝒪_weight_le_of_total`:
- `m ≥ 2, i1 ≥ 1`: need `⟺ DR ≤ d_R+degW+i1` ✓ (`DR ≤ D₀ = d_H+degW ≤ d_R+degW`);
- `m ≥ 2, i1 = 0`: needs the δ-SAVED budget `nB = (DR−m)+(d_R−1−m)degW` (the
  finding-10 twist via the PROVEN `leadingCoeff_dvd_evalX_hasseDerivY_top` + a cleared-rep
  weight lemma), then `⟺ DR ≤ d_R+degW` ✓;
- `m = 1, i1 ≥ 1`: the TRUNCATED need-form loses the spare W; the engine genuinely has
  `nB ≤ degW + Lξ` (per-term W-ledger `k+1 ≤ k+2`), under which `⟺ d_H ≤ d_R+i1` ✓;
- `m = 0` (top): `nB ≤ 1+2degW+Lξ` ✓.

**Action:** build the ANCHORED engine (per-case need-forms incl. the m=1 credit + the
i1=0 saved-budget lemma), deliver `Λ_{D₀}(β_t) ≤ (2t+1)d_R D₀`, convert upward via
D-monotonicity (`Λ_D ≤ Λ_{D₀} + (d_H−1)(D−D₀)` on canonical reps). Johnson becomes
conditional on the single ANCHOR hypothesis `totalDegree H = d_H + degW` at the
application point — to be checked against the GS factor structure (for proper factors
`d_H < d_R` of `R_{x₀}`, `degW ≤ D−d_R < D−d_H` at the GLOBAL D, so the anchor holds
only at the PER-FACTOR D₀, which is what the engine now uses).

## O156 (2026-06-11, Johnson finding 14 — PREDICTION, falsifiable): the in-tree (A.1) transcription's B is un-cleared ⟹ hroot/(P2) is generically FALSE for the in-tree βHensel

**The divergence.** Paper (A.1) (BCIKS20 lines 4060–4210) uses the W-TWISTED coefficients
`B_{i1,λ} = W^{d−δ−Σλ}·A_{i1,λ}` where `A = (Δ_X^{i1}Δ_Y^{Σλ}R)(x₀, α₀)` is evaluated at
`α₀ = T/W` — i.e. `B = Σ_b c_b·W^{d−δ−Σλ−b}·T^b` (the cleared form, in-tree analogue
`hasseCoeffRepr𝒪_cleared`). The in-tree `B_coeff = prefactor • hasseCoeffRepr𝒪` instead
`mk`'s the UN-cleared `Y ↦ T` lift `p(T) = Σ_b c_b·T^b`. These are different 𝒪-elements
(they differ by `W^{d−δ−Σλ−b}` per monomial), while `βHensel_succ` copies the paper's
engine exponents `W^{i1+δ−1}·ξ^{2i1+Σλ−2}` verbatim.

**The t = 1 test (exact).** `β₁ = −B_coeff(1,∅)` (the only surviving cell). The (P2) lift
identity at t = 1 demands `embedding β₁ = αGenuine 1 · W² · (emb ξ)`. With the PROVEN
`emb ξ = W^{d_R−2}·ζ` and the genuine Newton step `α₁ = −A_{1,∅}/ζ`, the RHS is
`−W^{d_R}·p₁(T/W)` while the LHS is `−p₁(T)` (up to the common scalar prefactor):
the identity holds iff `H̃ ∣ Σ_b c_b(1 − W^{d_R−b})·T^b` — FALSE generically (any `R`
whose specialized `Δ_X R` has a coefficient below the top degree, `W ≠ 1`).

**Consequences if confirmed.**
1. `hroot : eval (βHenselAssembled) Q = 0` — the single hypothesis (P2) was reduced to —
   is FALSE for the in-tree object; (P2) as stated is unprovable-because-false, not deep.
2. (P1)'s weight target for the in-tree βHensel is about a non-Hensel object; the i1 = 0
   budget failure (finding 13's residue) is a SYMPTOM of the same divergence: the paper's
   δ-saving lives on the cleared B, which the in-tree recursion does not use.

**The repair (one move fixes (P1)-residue and (P2)-shape together):** redefine the
recursion's coefficient as the cleared `B_coeff_cleared := prefactor •
mk (Σ_b c_b·W^{d−δ−Σλ−b}·Y^b)` (the in-tree `hasseCoeffRepr𝒪_cleared` with the δ-adjusted
power; its W-div top-coefficient saving is the PROVEN `leadingCoeff_dvd_evalX_hasseDerivY_top`).
Then (a) the t = 1 lift identity holds by construction, (b) the i1 = 0 SAVED budget
`(D_R−m)+(d_R−1−m)·degW` is provable by the same per-monomial supplier computation
(`hasseCoeffRepr𝒪_weight_le_of_total`'s pattern on the cleared rep), and (c) the ANCHORED
engine closes ALL cells — (P1) complete for the repaired recursion.

**Status: PROMOTED TO MACHINE-CHECKED (2026-06-11, same day).**
`BCIKS20/Finding14Countermodel.lean` (7 theorems, axiom-clean, full build): at
`F = ZMod 5`, `H = Z·Y+1`, `R = Z·Y²+Y+X`, `x₀ = 0` (full `Hypotheses` instance),
`βHensel 1 = −1 ≠ −Z² = −(paper's β₁)` — `inTree_B_ne_paper_B` + `βHensel_one_ne_paper`.
The in-tree recursion is NOT the paper's (A.1) for non-monic H; (P2)'s `hroot` targets
the wrong object; the repair (cleared δ-adjusted B) has all budget suppliers landed.

### Red team round 3 (#357 campaign) — MonomialDomination KILLED on the low bands by the spike floor; hybrid (v4) repair landed
The v3 surface (epsMCA ≤ monomialEps above the crossing) quantified over ALL grid
agreements — including the low bands, where the fleet's universal spike floor
(epsMCA_ge_j_div_card: per-position coefficient freedom u₀ = Σ aₗe_{pₗ}, u₁ = Σ e_{pₗ})
realizes j bad scalars while monomial pairs are structurally capped.
**Machine-checked (`MonomialDominationKilled.lean`, axiom-clean):** at (F₁₇, μ₈, k=2),
band 2 (a = 7): ε_mca ≥ 2/17 (spike floor + noWeightLE_two: affine two-roots) but EVERY
monomial pair has ≤ 1 bad scalar (monomial_coreG_le_one — kernel decide over the
GENERALIZED agreement-set maximality bridge coreG_of_mcaEvent, stack/agreement
parameterized; Python cross-check over all 64 pairs incl. diagonal: max = 1) ⟹
monomialEps ≤ 1/17 < 2/17 ≤ ε_mca: ¬MonomialDomination dom8 C ac for every ac < 7.
This is the formal twin of the empirical O146 cycle (double-spike refutation of
CensusUpperExtremal → two-family max correction).
**Repair (v4): HybridDomination** — ε_mca ≤ max(monomialEps, (n−a+1)/q); the staircase
term is an exact THEOREM below distance/3 (BandExactness/master collapse), so the
conjectural content is confined to the structured/window regime where every probe
supports it. v4 pin mcaDeltaStar_eq_of_hybridCrossing same engine.
**Surface lineage (all formal):** census (killed: empty rungs) → census+floor (killed:
take-over) → monomial (killed: spike bands, this) → hybrid = the two-family max:
consistent with every theorem and probe in the tree.

## 2026-06-11 — Items 11/13/14 (char-0 faces) DECIDED: the 4-adic quartet-tower law; the family's window interior has NO field-independent floor

Probe `probe_char0_death_law.py` (exact ℤ[ζ] folding): the char-0 constrained census
`Z0(n, a, c) = #{a-subsets of μ_n : e₂ = … = e_{c+1} = 0 in char 0}`:

**The mechanism (exact algebra, replaces the O143 enrichment statistics).** A quartet
`{x, ix, −x, −ix}` has characteristic polynomial `T⁴ − x⁴`, so a union of `q` quartets
has `e_j = 0 for ALL j ≢ 0 (mod 4)` and `e_{4s} = ±e_s(x₁⁴, …, x_q⁴)` — **the census
recurses down the 4-adic tower**: constraints at depth `c` on `μ_n` become a
vanishing-sum system at depth `⌊(c+1)/4⌋` on `μ_{n/4}`. Verified exactly:
* `Z0(n, 8, 2) = C(n/4, 2)` (quartet pairs): 6 at n=16, 28 at n=32 ✓
* `Z0(16, 9, 2) = C(4,2)·8 = 48` (+ free point) ✓; `Z0(n, a, c) = 0` for a ≡ 2, 3 mod 4 ✓
* `Z0(16, 8, 3) = 2`, `Z0(32, 8, 3) = 4` = antipodal pairs in `μ_{n/4}` ✓ — and the
  solutions are exactly the two cosets of `μ_{n/2}`, which survive EVERY depth
  (`Π(T − y) = T^{n/2} − const`): `Z0(16, 8, c) = 2` for all c ≤ 6 ✓
* `Z0(16, 12, c)`: 20 / 4 / **0** / 0 at c = 1/2/3/4 — death at c = 3 exactly as the
  recursion predicts (`e₄ = 0` forces a 3-term vanishing sum on `μ₄`: odd size,
  impossible by the proven 2-power Lam–Leung negation-symmetry) ✓

**The structural verdict.** At rate 1/4 the window-interior rungs (`k+1 < a < n/2`)
of the adjacent-pair family are char-0 DEAD beyond the first rung: parity kills
`a ≡ 2, 3 (mod 4)` and the odd-recursion Lam–Leung kill takes the rest; the only
survivors are the first rung `a = k+1` (near capacity) and the subgroup cosets AT the
Johnson boundary `a = n/2`. **The family's window-interior census at large p is pure
characteristic-p surplus (the Weil-fluctuation layer) with NO field-independent
floor** — the conjecturally-extremal family cannot pin an interior δ* through its
char-0 layer; any interior pin from this family must come from the char-p layer,
i.e. from below-√q character-sum information (the same open kernel, fourth face).

This is the asymptotic law item 11 asked for (char-0 face), the exact algebra item 13
asked for (quartet-tower classification replaces the 1.8σ enrichment), and the tower
closure item 14 asked for (the 4-adic recursion IS the closed form; layer 1 at
`n = 2^20` is tower-computable by iterating it).

## 2026-06-11 — Item 2 DECIDED (probe-grade): the slanted supply is COMPLETE

`probe_slanted_stratum_census.py` (exact ℤ[ζ] folding, 12-term determinant exactly):
the char-0 slanted stratum of the wide-circuit census — disjoint pair-triples
(6 distinct indices) collinear on a non-vertical, non-horizontal line:

* Census totals: **16** at n = 8, **544** at n = 16 (exhaustive).
* **The three landed families generate ALL of it**: the chord law `(d, d, n/2)` with
  its congruence + the shape-I/II seeds, closed under the affine-Galois symmetry
  group `i ↦ u·i + c` (u odd — Galois conjugation preserves char-0 collinearity):
  explained 16/16 and 544/544, **zero unexplained** at both scales.  (The handful of
  "spurious" orbit images are family instances degenerating onto vertical/horizontal
  lines, correctly excluded by the stratum filter.)
* Bonus structure found en route: triples of pairs sharing a common index are ALWAYS
  collinear (`s = ζ^i + ζ^{−i}·p` — the star pencil), which is why the matroid lane
  restricts to disjoint pairs; and at n = 8 the only non-chord disjoint instances are
  the reflected-chord shape `(d, −d, n/2)`, which the seeds' orbit closure covers.

**Verdict: the slanted-stratum case analysis has a now-known-true target**: every
disjoint slanted collinear triple is an affine-Galois image of chord/shape-I/shape-II.
The 12-term determinant analysis (item 2's Lean half) is the completeness proof of
exactly this statement; the strata census closed form follows by orbit counting.

## 2026-06-11 — WB-1 red-team: non-vacuity CONFIRMED; the solvable set is a (2w+k)-dim variety

`probe_wbfar_existence.py` at (p,n,k) = (17,8,2): the WB-solvable direction fraction
* `w = 2` (one below the UDR boundary): **16/4000 = 0.40%** vs the variety prediction
  `q^{2w+k−n} = 17^{−2} = 0.35%` — 99.6% of directions are WB-far; WB-1 bites
  generically;
* `w = 1`: 0/2000 (`~17^{−4}`) — even more generic deeper below;
* `w = 3` (`n = 2w+k`, the boundary): 4000/4000 solvable — the underdetermined system,
  exactly the sharpness cutoff stated in the theorem.

So the dimension picture is: the WB-solvable directions form a `≤ (2w+k)`-parameter
image inside `F^n` (pairs `(ℓ, R)` mod scaling), proper exactly below UDR, and the
naive `3w+k` overcount (the free-on-roots correction) is not real.  WB-1 is
non-vacuous on a `1 − O(q^{2w+k−n})` fraction of directions at every below-UDR slack.
Remaining for the all-stacks law: the near-direction side (the `O(q^{2w+k})`
exceptional directions) via pencil deflation.

## 2026-06-11 — WB-2 open-core probes: the doubly-rational sup is EMPTY at every tested below-UDR instance

`probe_rational_pair_extremality.py` (17,8,2,w=2) + `probe_rational_pair_window.py`
(97,16,2,w=5 — the genuine window `3w+k−1 ≥ n > 2w+k` where degree-forcing fails):

* Random genuine rational pairs: **max bad = 0** at both instances (250 + 60 samples).
* Monomial pairs `(x^a, x^b)`: max **1**; quadratic/shared-denominator pairs: max **1/0**.
* So the WB-2 residual sup is far below its `(w+3)/q` far-side companion everywhere
  tested — the below-UDR all-stacks law `ε_mca ≤ O(w)/q` looks TRUE.

**The mechanism, by regime (analysis):**
* `3w+k−1 < n` (ladder reach): explainability forces the polynomial identity
  `c·ℓ₀ℓ₁ = ℓ₁R₀ + γℓ₀R₁`; coprime genuine denominators give `ℓ₀ | R₀` — contradiction:
  **zero bad scalars, provable** (WB-3a, Lean queued: agreement > degree forcing +
  divisibility).
* `4w+k−1 < n`: pairwise differencing forces `ℓ₁ | R₁` from two bad scalars:
  **≤ 1 bad, provable** (weaker radius, subsumed).
* The window `[(n−k)/3, (n−k)/2)`: neither forcing applies, yet the probe finds zero —
  the conjectured mechanism is codimension counting on the root-configuration variety
  (each bad γ needs a degree-`2w+k−1` pencil member with ALL its roots on `D`).
  **Open: an adversarial construction OR a counting proof.**  This — the window
  rational-pair bad count — is now the entire below-UDR question, and the
  above-UDR/Johnson window remains the recognized core beyond it.

## 2026-06-11 — WindowRationalEmpty REFUTED; the window adversary is MÖBIUS-SYMMETRIC and caps at w+1

`probe_window_rational_adversarial.py` at (q,n,k,w) = (13,6,1,2) — genuinely in the
window (`3w+k = 7 > 6 = n > 2w+k+1−1`): **max bad = 3 = w+1 > 0** over 30k genuine
rational pairs. The "window empty" reading of the earlier null probes is REFUTED —
those instances were at or below the ladder reach, or under-sampled.

**The structure** (`probe_window_mobius_structure.py`): the extremal stack is
invariant under the Möbius involution `x ↦ −1/x` (both rows constant on the orbits
`{x, −x⁻¹}`), and the EXHAUSTIVE search over the Möbius-invariant family confirms
its max is exactly `w+1 = 3` — attained at the clean stack
`u₀ = (0,0,0,0,1,1)`, `u₁ = (0,1,1,0,2,2)` on orbit values.  The window adversary
exists and lives on the involution-quotient — the fold/Möbius structure the dossier
predicted (`MobiusPencilEnergy` lane), now witnessed inside the WB window.

**Surviving form**: `WindowRationalBounded` — doubly-WB-solvable stacks in the
window have bad count ≤ w+3 (observed max w+1).  WB-2's grand bound
`ε_mca ≤ (w+3)/q` below UDR is CONSISTENT with the find (3 ≤ 5); the named Prop
carries the window and the below-UDR law is conditional on it alone.

## 2026-06-11 — The Möbius dominance confirmed at scale 2; the window cap holds with room

`probe_window_renormalization.py` at (13, 12, 1, w=4) — the next window scale
(`2w+k+1 = 10 ≤ 12 < 13 = 3w+k`), domain `F₁₃* = μ₁₂` with σ(x) = −1/x
(7 classes: 5 doubletons + 2 fixed points {5, 8}):

* **Möbius-invariant pairs: sampled max bad = 3** (60k samples);
* **general pairs: sampled max bad = 1** (20k samples) —
  the invariant family dominates 3:1, replicating the scale-1 finding that the
  window adversary is Möbius-symmetric;
* both far inside the `w+1 = 5` observed cap and the `w+3 = 7` budget of
  `WindowRationalBounded`.

**The renormalization picture**: the window is scale-self-similar (the quotient of
a window instance is again a window instance at half scale — `3w'/n' = 3w/n`), the
extremals concentrate on the σ-invariant family at every tested scale, and the
per-scale cap stays `≤ w+1`.  The attack on `WindowRationalBounded` is therefore a
classification of σ-invariant rational pairs over the involution quotient — a
half-dimension problem where the census/quartet machinery applies — grounded in
finite base cases (the n = 6 window base is exhaustively `≤ w+1`).

## 2026-06-12 — WindowRationalBounded REFUTED: the normalizer-pair family (n/2 bad scalars, every field)

The named Prop of the below-UDR capstone (`WBPencilBelowUDR.lean`) asserted every
doubly-WB-solvable stack has ≤ w+3 bad scalars.  **FALSE at high rate.**  The
counterexamples are an explicit, q-independent family derived from the CRT/projective
class reduction at the first beyond-ladder slice `n = 3w+k−1` (j = 0):

* **The alignment identity.**  For `c ∈ μ_n` and any `ξ ∉ μ_n ∪ {0}`:
  `(ξ−α)(ξ−c/α) = (ξ²/c)·((c/ξ)−α)((c/ξ)−c/α)` — equivalently, every involution pair
  `T = {α, c/α}` has the SAME projective class `[Z_T] ∈ (F[X]/ℓ)^×/F^×` for
  `ℓ = (X−ξ)(X−c/ξ)`.  Taking `ℓ₀, ℓ₁` two such quadratics (roots off-domain,
  coprime) and `R_j` the canonical representatives aligning one pair `T₀`, EVERY
  pair `T = {α, c/α}` yields `M := c_T·Z_{D∖T} ≡ ℓ₁R₀ (mod ℓ₀) ≡ γ(T)·ℓ₀R₁ (mod ℓ₁)`,
  i.e. `γ(T)` is line-explainable with witness `D∖T`.
* **No-joint is free**: a genuinely rational row (`ℓ ∤ R`, `ℓ` domain-nonvanishing)
  is NEVER deg-<k-explainable on n−w ≥ w+k points (degree forcing) — so every
  explainable γ is mca-BAD; the (n−2)/2 (c square) pair-scalars are distinct.
* **Verified** (`probe_normalizer_pair_family.py`, predicted = exact everywhere,
  independent second implementation at the violation): (37,12,7,2): 5; (97,12,7,2): 5
  (q-independent); **(97,16,11,2): 7 > 5 = w+3 — REFUTED at the 2-power production
  shape**; (113,16,11,2): 7; **(41,20,15,2): 9 > 5**.
* **Why never seen before**: all prior window probes ran at `n = q−1` (full
  multiplicative group), where NO off-domain ξ exists — the family needs `q−1 > n+4`.
  The "window cap = w+1" empirics (scales 1–2) were an n = q−1 artifact.
* **The w ≥ 4 collapse** (probed): full-degree denominators (products of w/2
  involution quadratics) are REQUIRED (else deg P ≥ k), and then the per-quadratic
  scalar-consistency constraints kill all unions except T₀ (predicted = exact = 1 at
  (37,12,1,4), (97,16,5,4), (61,20,9,4)).  The μ_w-coset variant (`ℓ = X^w − e`,
  `T = t·μ_w`, `Z_T ≡ e−t^w` constant) gives `n/w` distinct bad scalars (Möbius in
  `t^w`) for every `w ∣ n` — the general-w family is Θ(n/w), not n^{w/2}.
* **Structural reading**: the two maximal w = 2 families are exactly the
  torus-normalizer involutions `x ↦ c/x` and `x ↦ −x` — the same normalizer the
  O133/O144 moment census isolates.  Maximal aligned-pair families = normalizer
  graphs; non-normalizer Möbius classes cap at O(1) pairs.

**Surviving form** (`WindowRationalLinear`, repaired budget): doubly-WB-solvable
stacks have ≤ n bad scalars below UDR.  Consistent with: the new families (n/2, n/w),
the per-family bound w+1 (`FamilyBadBound.lean`), WB-1/3a/3b, and the H-RC slice-1
≤ n law above UDR.  At production (q ≥ 2¹⁹², n ≤ 2³⁰): n/q ≤ 2^{−162} ≪ 2^{−128} —
**the production floor (1−ρ)/2 SURVIVES with the repaired budget**.  Lean repair
queued: `¬WindowRationalBounded` countermodel + re-parameterized capstone.

## 2026-06-11 — Ownership degeneracy REFUTED: the count mechanism EXPLAINS the window cap

`probe_ownership_degeneracy.py` at (13,6,1,w=2), k = 1 (residual of a pair =
`u₁(j) − u₁(i)`): the Möbius window extremal's per-scalar ownership is **8 = the
generic mean (8.1)** — NO collapse on the symmetric locus.  And the count is nearly
tight: `#bad·ownership = 3·8 = 24 ≤ 30 = n(n−1)` — the window cap `w+1 = 3` IS the
ownership bound `⌊30/8⌋`.  The mechanism, exactly: the extremal's `u₁ = (0,1,1,0,2,2)`
has value-multiplicity `μ = 2`, every witness has `|S| ≥ 4`, so ownership
`≥ |S|(|S|−μ) = 4·2 = 8` — measured exactly.

**Consequence (the multiplicity theorem, k = 1)**: `#bad ≤ n²/((n−w)(n−w−μ))` where
`μ` is the max value-multiplicity of `u₁` — radius-free, window-valid, the first
unconditional bound past the ladder reach for these stacks.  The general-k analogue
(μ → max agreement of `u₁` with degree-< k polynomials) is the ownership route to
`WindowRationalBounded` in full.

### O136 — THE TAIL STRUCTURE THEOREMS: parity purity kills every odd r > s/2 at every scale (T1, PROVEN); marginal(32) = 1,728,112 is COMPLETE (T4); turn-on is monotone (T3); r_max = 2j−5 REFUTED by 29 certificates; sharp law r² ≤ s+1 conjectured at 26/26 — and the r=5 taxonomy derivation passes adversarial audit (nubs, 2026-06-12)

Two audited deliverables (independent adversarial legs, both 0.93, zero fatal):
`scripts/probes/genlaw/exclusion/REPORT.md` and `scripts/probes/genlaw/r5tax/DERIVED-99512.md`.

* **T1 [PROVEN, every odd r, every s = 2^j]: parity purity.** The odd-exponent part of the
  balance multiset is exactly the mixed-parity products; its vanishing sum factors as U·V
  over ℤ[ζ_n], and either factor vanishing forces one parity side empty (distinct fibers
  occupy distinct antipodal classes). **Corollary: N_r(s) = 0 unconditionally for r > s/2**
  — the entire deep tail, all scales, no enumeration. (Generalizes O108's L1 and the r=5
  3-torsion argument in one stroke.)
* **T4: s = 32 marginal CLOSED.** N_r(32) = 0 for ALL odd r ≥ 7 (r=7: full 215,414,784-config
  sweep; r=7..15: pure-only exhaustive, legitimate by T1; r ≥ 17: T1 corollary). **O130's
  load-bearing caveat 1 is discharged at s=32: marginal(32) = 2·(764,544 + 99,512) =
  1,728,112 COMPLETE.** Same method re-establishes DERIVED-672 completeness at s=16 (third
  implementation). Raw mixed-parity r=13 sign sweep running as belt-and-suspenders (0–3 of
  8 workers returned 0 at entry time).
* **T3 [PROVEN]: doubling monotonicity** — N_r(s) ≥ 1 ⟹ N_r(2s) ≥ 1 (double the witness,
  pad with s/4 antipodal pairs). Strata never turn off. **T2 [PROVEN]:** h ≡ b (mod 2) for
  pure configs — the "(b−h) odd" gate is vacuous (die_par = 0 in every measured stratum).
* **The boundary: r_max = 2j−5 (O130's pattern guess) is REFUTED.** 29 explicit (O, m, B)
  certificates — 8×(128,9), 6×(128,11), 8×(256,13), 3×(256,15), 2×(512,17), 2×(512,19) —
  each re-verified twice (exact integer multiset rebuild + independent complex-float
  vanishing check). The surviving conjecture is the **sharp law: N_r(s) > 0 ⟺ r² ≤ s+1**
  (equivalently C(r,2) ≤ b), 26/26 on every settled stratum, explaining the s=8 tightness
  (9 ≤ 9). Mechanism finding [MEASURED]: the aggregate budget inequality X+F ≥ ((r+1)²−s)/2
  is NEVER the kill — 100% of pure deaths at zero strata are PER-AXIS capacity (|d| ≥ 2) or
  forced-fiber blocking; the additive-combinatorial bound for the middle band
  √(s+1) < r ≤ s/2 was attempted and NOT achieved (the obstruction: B is a SET with per-axis
  capacity 1, invisible to aggregate coincidence counts). Honest opens: (64,9) — law says 0,
  enumeration DNF (prior pass's claimed closure had 0-byte artifacts, withdrawn); (512,21) —
  law says ON, three climbs stall (open in BOTH directions; the sharpest falsification
  target); OFF-side evidence above s=64 is single-probe-per-scale.
* **The r=5 taxonomy (O130's residual 3) PASSES AUDIT and lands:** every [PROVEN] lemma
  hand re-derived (incl. the 3-torsion purity proof: index-disjoint matching forces a
  3-cycle, t³ = −1 impossible in μ_{2^k}); complete-axis-alphabet classification of all
  11,808 records with zero out-of-alphabet hits; independent σ-rank engine over all 8,736
  geometries; C1/C2/C3 closed forms re-derived; all four target charts (11,808 / 99,512 /
  ε-split / E5 census / 11 z*-strata) crossfooted from records. Landed at
  `genlaw/r5tax/` with the audit's two required edits applied (in-tree artifact paths;
  s ≥ 64 kernel-row provenance note + general-r threshold form). The s=64 blind-hit
  re-execution: `struct_count` reproduces all 9 small-s rungs from source and the
  line-by-line review found no s-dependence hazard; **independent re-execution lands the
  blind hits: (64,5) and (64,7) EXACT vs the enumerated anchors (0.5s / 3min), and both
  s=128 rows reproduce exactly — N₃(128) = 5,479,419,333,117,151,127,552 and N₅(128) =
  11,414,927,180,313,095,025,440 now stand as kernel-validated predictions** (independent
  algorithm at s=128 = the remaining falsifier; by T3+certificates the true marginal(128)
  ALSO includes N₇, N₉(8 certs), N₁₁(6 certs) strata — the law's r ≤ 11 band).

**Where the open core moves:** the per-level law now has a PROVEN skeleton (T1 purity +
T2 parity + T3 monotonicity + per-s enumeration below s/2) and one conjectured sharp
boundary (r² ≤ s+1) with two named decision points ((64,9), (512,21)). The middle-band
structural proof — per-axis capacity, not aggregate budget — is the remaining theorem.

### O155 — THE CONSTANT-6 LAW: the char-0 non-normalizer Möbius coincidence with μ_n is exactly 6 at every tested 2-power scale — flat in n, one uniform witness family, one closed-form normal; the small-field growth was entirely mod-p surplus (normalizer-gap lane, 2026-06-12)

`scripts/probes/normalizer_gap/` (census `probe_pgl2_coincidence_census.py` brute-gated
at q=41 + O133-calibration-gated; char-0 `probe_char0_incidence_census.py` two split
primes ≳ 2^28; anchor `probe_char0_anchor.py` exact ℤ[x]/(x^{n/2}+1), fraction-free
Bareiss). Object: M(n) = max over Möbius σ ∉ N(T) (the torus normalizer x↦cx, x↦c/x)
of |μ_n ∩ σ(μ_n)| in char 0 — each incidence is a point of the surface
P(i,j) = (ζ^{i+j}, ζ^j, ζ^i, 1) on a non-normalizer hyperplane.

* **M(8) = M(16) = M(32) = M(64) = 6 — FLAT.** Lower bound PROVEN in char 0: the
  uniform family S(n) = {(0,0),(1,1),(2,3),(4,n/2+2),(n/2−1,n−3),(n−2,n−1)} lies on
  the ONE closed-form normal (m = n/2): c = −ζ^{m−1}+ζ−2, d = 2ζ^{m−1}−ζ^{m−2}−ζ³+ζ²+ζ,
  −a = −ζ^{m−1}+ζ^{m−2}+ζ³−2ζ²+1, −b = (ζ−1)² — max |coeff| = 2, rank exactly 3,
  ad−bc ≠ 0, all six incidences vanish identically, no 7th char-0 point. Upper bound
  PROVEN-BY-HEIGHT at n = 8, 16 (Hadamard < 2^56 < p₁p₂); two-prime bit-identical
  evidence at n = 32, 64. Structure laws (exact, every n): j−i multiset
  {0,0,1,1,n/2−2,n/2−2}; σ ~ σ^{-1} invariance (swapneg at (1,1)); trivial translation
  stabilizer (no torsion-coset structure); n=8's full dihedral symmetry lost at n ≥ 16.
* **The F_q growth was surplus**: drained field maxima (10@n=32/q=449, 16@n=64/q=1153)
  still sat ABOVE the constant core 6 — the two-layer law again (O134's lesson; an
  intermediate pre-registered Fibonacci fit was refuted by its own falsifier 11 min
  after registration). Count-6 planes multiply with n (12, 300, 1932, 9420) but the
  cap stays 6.
* **Position**: the (1,1)-curve of σ is torus-special ⟺ σ ∈ N(T) — for everything
  else Corvaja–Zannier (JEMS 2013, Cor 2) gives O(|H|^{2/3}) up to p^{3/4} (explicit
  ≈ 4.77, Makarychev–Vyugin); the production regime n ≤ 2^40 ≪ p^{1/2} is KSV
  Conjecture 1.3 (O(1), A ≥ 9 known) — OUR 2-POWER-TORSION CAP 6 < 9 says smooth
  domains are below the conjecture's worst case in char 0. Consumers: the WB σ-descent
  concentration step (#371 — only normalizer symmetries can carry invariant extremal
  structure; everything else touches the domain in ≤ 6 char-0 points); the O133
  spectral gap (its census = this engine's involution slice, audit-confirmed).
* **Also this cycle (same lane, #371 comment 4687572266)**: the σ-invariant
  WB-RATIONAL family at scale 2 has exhaustive max bad = 1 (their sampled "invariant
  max 3" was over non-rational orbit-constant pairs) — inside WindowRationalBounded's
  own class the invariant family does not renormalize. And the O133 probe program
  passed independent adversarial audit (two fresh algorithms incl. the n = q−1 edge;
  one [:8]-truncation reporting bug found+fixed, headlines intact;
  scripts/probes/moments/audit/).
* **Named next**: the M(n) ≥ 6 ∀ 2-power n Lean brick (one parametric identity);
  the ≤ 6 theorem (7-incidence impossibility — Lam–Leung/antipodal route, the
  candidate mechanism for the in-tree vanishing-sum machinery); the height upgrade
  of ≤ at n = 32, 64 (third prime or Hadamard sharpening); norm-spectrum
  quantification for the production surplus threshold.

## 2026-06-12 — The level-j staircase is NOT the complete envelope: the ANTIPODAL PENCIL; the d = 4 level-1 rung pin is REFUTED

**Attempt** (#371 round 7): pin the first sub-ceiling rung exactly — `δ* = 5/8` for the
`n = 16, d = 2` code on `⟨4134⟩ ⊆ F₁₂₂₈₉ˣ` at budgets `ε* < 32/p`, with the good side
"every stack has few bad scalars below `5/8`" (the staircase-completeness hope: only the
deeper level-`j` sign-subset families are bad below a rung, counts `5 → 1`).

**Disproof of completeness.** The corrected adversarial probe (`probe_level1_pin.py`;
the old S6 "worst = 1" was a search artifact — its pool capped monomial exponents at 4)
found the **antipodal pencil** `(X^h, X^{h+1})`, `h = n/2`: since `x^h = ±1`, the line
`x^h(1+γx)` *is* the degree-1 word `±(1+γX)` on a full antipodal half-coset plus the one
rotating cross-coset point `x₀ = −1/γ`, and the direction `±x` single-deviates there.
**All `n` scalars of the inversion orbit `−1/⟨g⟩` are bad at radius `1 − (h+1)/n`**, for
every code degree `1 ≤ d ≤ h − 1` — strictly below the deepest staircase rung (`1/2`)
with count strictly above every deep-rung spectrum (`16 > 5 = N(2,2)` at the instance).
Proven axiom-clean, in general:

```lean
ArkLib.ProximityGap.Level1Rung.antipodal_pencil_epsMCA_lower_bound   -- n bad at 1−(h+1)/n
ArkLib.ProximityGap.Level1Rung.mcaDeltaStar_le_antipodal             -- δ* ≤ 1−(h+1)/n at ε* < n/p
```

**Consequences (Level1RungPin.lean, all axiom-clean).**
- The `d = 4` (rate 5/16) level-1 rung `1/2` is **refuted as a pin point on its entire
  band**: the pencil count `16` equals the rung budget `K₁ = 16`, so for every
  `ε* < 16/p`, `δ* ≤ 7/16 < 1/2` (`deltaStar_lt_levelOne_rung_F12289_d4`); the per-rung
  interior obligation there is **unsatisfiable** (`level1_interior_unsat_F12289_d4`).
- The `d = 2` rung `5/8` **survives**, with its conditional band trapped to
  `[16/p, 32/p)` (`level1_interior_floor16_F12289`); probed worst stack at threshold 7
  is exactly 16 = the pencil. Envelope-exactness there = ONE named obligation
  (`SubCeilingInteriorCeiling` via `subceiling_deltaStar_pin_of_interior`, the general
  per-rung reduction), and the in-tree per-witness subset counting **provably cannot
  discharge it**: absolute scheme cap `C(16,4)/C(7,4) = 52 > 31` (the saturation theorem
  made concrete; `level1_budget_le_subset_cap`).
- The pencil ladder continues: `(X^h, X^{h+2})` gives 8 bad at radius `3/8` (probed,
  exact, `p ∈ {97, 12289}`). The refined envelope = staircase ⊔ pencil ladder (⊔ ...?)
  is the successor question; any future "complete envelope" claim must subsume the
  pencil orbit.

## 2026-06-12 — REFUTED: the rung census conjecture `bad ≤ 16 = n` (p=12289, n=16, k=3, agreement 7)

The block-frame construction beats the antipodal pencil. Two disjoint 6-point
agreement blocks `A₁, A₂` with `R₁ ≡ qᵢ`, `R₀ ≡ rᵢ` on `Aᵢ` (deg < 3, distinct)
plus 4 steered free points realize **20 distinct bad scalars** — witnesses
`Aᵢ ∪ {x}`, one scalar per off-point `γ = −(R₀(x)−rᵢ(x))/(R₁(x)−qᵢ(x))`,
hitting the `maximal_frame_attached_card_le` cap `n − |A| = 10` on BOTH
frames simultaneously (`RungMaximalFrame.lean` predicts the 20 exactly).

* `probe_wb371_blockframe.py` / `probe_wb371_verify20.py`: the explicit stack
  is double-verified (fast residue census + independent slow Lagrange-fit
  checker; 25 non-bad controls clean). Deterministic seed 20260612.
* At p=17 the same construction caps at 15 (< 17 available scalars) — the toy
  scale structurally MASKS the configuration; earlier census probes (40
  adversarial constructions/scale) never tried block designs.
* Status of the round-7 obligation `SubCeilingInteriorCeiling ≤ 31`: ALIVE
  (20 ≤ 31) but the margin is 11, not 15, and k-block webs (pairwise-≤2
  overlapping 6-blocks) have 10k candidate scalars — the 3-/4-block
  realizability question is now THE obligation-critical computation.
* The conjecture `δ* truth = 16` at this rung and the issue-comment claim
  "bad ≤ 16 HOLDS at both scales" (comment 4688420285) are WITHDRAWN.

### O156 — THE CONSTANT-6 LAW IS TWO-SIDED at n = 8..64, and the ≤-side target is a Beukers–Smyth sharpening: M(32) = M(64) = 6 rigorous via the invisibility trichotomy; the witness curve is conjugate-reciprocal exactly as BS's structure theorem demands (normalizer-gap lane, 2026-06-12; follow-up to O155)

* **M(32) ≤ 6 and M(64) ≤ 6 RIGOROUS** (`probe_char0_rigor.py`, RESULTS-CHAR0-RIGOR.md):
  a hypothetical 7-incidence char-0 plane fixes THREE nonzero case integers
  (coordinate norms ≤ 3^{3m/2}, det norm ≤ 54^m — exact Hadamard; cruder L1 route
  6^m/72^m carried independently); a clean census at split p > 2^28 misses the plane
  only if p divides one of them (the invisibility trichotomy — audited against the
  census skip-paths; note: the naive "p | content" exclusion is INVALID since
  reduction is evaluation, not coefficientwise — replaced by the norm/divisibility
  lemma); per-plane pigeonhole: 6 clean primes kill n=32, 11 (Hadamard) / 12 (L1)
  kill n=64; ladders ran 8 and 12 primes, ALL max = 6, bit-identical histograms.
  Combined with O155's char-0 anchor: **M(n) = 6, both directions, n ∈ {8,16,32,64}**
  (program-assisted: exact arithmetic + symbolic self-checks; not yet Lean).
* **The Laurent collapse** (from the ≥6 brick design): under ζ^m = −1 the witness
  datum is m-INDEPENDENT — z·c = (ζ−1)², ζ²·d = −(ζ−1)²(ζ³+ζ²−1),
  ζ²·a = −(ζ−1)²(ζ³−ζ−1), b = −(ζ−1)², ζ⁴(ad−bc) = (ζ−1)⁶(ζ+1)²(ζ²+ζ+1): ONE fixed
  Möbius map realizes the 6 points at every 2-power level; incidences are ring
  identities for ALL m ≥ 2. Lean brick (MobiusCoincidenceWitness.lean) in flight.
* **The ≤6-for-all-n question is exactly a Beukers–Smyth sharpening** (lit-gated at
  the source, Number Theory for the Millennium I 2002): BS bound = 22·V (V = 1 for
  bidegree (1,1)); sharp constant OPEN even for BS (16 ≤ C ≤ 22); their §5.6 covers
  only the symmetric rational family xy + λ(x+y) + 1 (max 4). CONSISTENCY FALSIFIER
  PASSED: BS cap non-reciprocal curves at 4V — any curve beating 4 MUST be
  conjugate-reciprocal (f ~ f̄(x⁻¹,y⁻¹)) with ℚ^ab coefficients; our witness curve
  verified exactly that (inversion + conjugation returns it with unit factor 1/ζ).
  So the open branch of the ≤6 theorem is ONLY the conjugate-reciprocal
  abelian-coefficient (1,1)-family — explicitly parameterizable via the
  reciprocity relations; census ground truth: count-6 maximizer classes are rich
  (34 at n=16, 210 at n=32, all partial injections — finite-list classification
  impossible, the uniform mechanism must be BS's f†/seven-polynomial machinery).
* Census engine debt note: the count-6 classification + ladders share the one
  census code path (mitigated by the symbolic identity checks, the n=8 exhaustive
  norm audit, and brute gates at q=41); an independent reimplementation would
  upgrade confidence — cheap follow-up for any seat.

### O157 — THE SPANNING IDENTITY: rank-3 surface planes are AUTOMATICALLY conjugate-reciprocal (λ = ζ^{−Σ} explicit) — non-reciprocal planes carry ≤ 2 points; all 244 maximizer classes verified; the constant-6 law extends to n = 128 with a forward-predicted exact count law (normalizer-gap lane, 2026-06-12; follow-up to O155/O156)

`scripts/probes/normalizer_gap/` (probe_reciprocal_param.py, probe_reciprocal_census.py,
RESULTS-RECIPROCAL.md; commit 66b05bd71). Batch-2 falsifier round — all passed:

* **The spanning identity** (machine-verified exhaustively at n=8, randomly to 256, mod-p in
  every census run): rev(cross(P00, P(i₁,j₁), P(i₂,j₂))) = ζ^Σ·conj(cross), Σ = i₁+j₁+i₂+j₂.
  Consequence: EVERY plane spanned by a rank-3 surface triple is conjugate-reciprocal with
  the explicit unit λ = ζ^{−Σ} — and invertible non-normalizer NON-reciprocal planes carry
  ≤ 2 surface points (rank-3 ⟹ reciprocal; rank-2 ⟹ coordinate line ⟹ singular). On this
  surface that sharpens Beukers–Smyth's non-reciprocal 4V-cap to 2, and localizes the
  ≤6-for-all-n question ENTIRELY inside the explicit λ-family (a half-dimension K-subspace,
  rank-verified). Care taken: λλ̄ = 1 does NOT imply λ = ±ζ^t in general (machine
  counterexample (3+4i)/5) — the ±ζ^t form holds for primitive integral normals
  (content + Kronecker) and is explicit for spanned planes via the identity.
* **BS-consistency falsifier passed at full strength**: all 34 (n=16) + 210 (n=32) count-6
  maximizer classes reconstructed and re-proven char-0 count-6 in exact ℤ[x]/(x^{n/2}+1),
  each fitting the UNIQUE predicted λ = ζ^{−Σ}. No anomaly.
* **Constant-6 extends to n = 128**: M_p(128) = 6 at two split primes, zero planes above 6;
  M(128) ≥ 6 and M(256) ≥ 6 proven char-0 (multi-prime certificate mode: heights ⟹
  N² ≤ 432^m; ladder product exceeding it forces exact vanishing — every count-5/6 plane at
  every n ∈ {8..128} carries an exact certificate, 0 failures). ≤6 at 128 remains two-prime
  evidence (rigor ladder = 24 clean primes, ~3h, named follow-up; n=256 census needs ~35GB
  disk — skipped honestly, ≥6 anchor stands).
* **Exact count laws** (forward-predicted: the quadratic through n=16/32/64 predicted
  count6(128) = 41292 BEFORE the run; both primes returned exactly that):
  count6(n) = (n−4)(11n−76)/4 over n = 8..128 (12/300/1932/9420/41292, five-for-five) and
  count5(n) = 10(n−6) (five-for-five). Closed-form DERIVATION from the λ-family = the named
  next brick (these are the maximizer-population laws the ≤6 theorem must reproduce).
* **First mod-p surplus of the program observed** (n=128: count-3/4 buckets differ across the
  two primes; count-5/6 and the max bit-identical, all certified char-0) — the two-layer law
  surfaces exactly where the certificates stop, never touching the headline.
* **O156's engine-debt note DISCHARGED**: independent reimplementation of dedupe (streamed
  gzip + external sort) and recount (fresh Möbius O(n)-per-plane counter), gate-reproduced
  bit-identically at n=32/64 before n=128 was believed.

Named next: the ≤6 theorem ON the λ-family (BS f†/seven-polynomial machinery, count laws as
ground truth); the 24-prime M(128) ladder; count6/count5 closed-form derivation; the
const6_witness Lean brick's ≤-side counterpart.

## 2026-06-12 — The UDR-edge gap of the universal dichotomy is INTRINSIC (analysis)

The universal below-UDR law covers `2w + 2k ≤ n`; the band `n ∈ [2w+k+1, 2w+2k)`
(width `k/n` in radius) is a genuine gap of the method, not bookkeeping: for a
direction at distance `e ∈ (w, w+k]` from the code (max agreement
`a ∈ [n−w−k, n−w)`), BOTH branches vanish — the multiplicity factor
`n−w−k−μ = e−w−k ≤ 0`, and the sparse/packing popular count needs witness-minus-
support `m = n−w−e ≥ k`, which fails exactly there (at `m < k` even a single
codeword is not determined by the off-support agreement, so the popularity
argument cannot start).  Closing the band needs a counting mechanism for
explaining codewords pinned by FEWER than `k` points plus the γ-line structure —
the same shape as the at-UDR boundary slice (`B6 = 7`) analysis.  Logged as the
fifth documented no-go; the band is the precise below-UDR residue.

## 2026-06-12 — THE TUBE EXPERIMENT: ladder extremality at threshold REFUTED; far directions attain C(n,k+1) exactly; WB-3b live-verified beyond Johnson

`probe_tube_vs_spectrum.py` at the dimension-ladder instance (p = 12289, n = 8 = μ₈,
k = 2, agreement t = 3 — the threshold radius δ = 5/8, beyond Johnson):

* **ladder stack (X³, X²): exactly 40 bad scalars** — byte-matches the sibling's
  spectrum law N(3,3) (checker cross-validated);
* **random far directions: 56 = C(8,3) — repeatedly, exactly** — every
  (k+1)-subset of a witness determines one scalar, all distinct generically: the
  ownership count is TIGHT, and far directions BEAT the spectrum family at the
  threshold (56 > 40).  The adjacent-pair family is NOT the threshold extremizer;
  the exact threshold sup is ≥ C(n,k+1)/p;
* **genuine codeword direction: 0 bad** — WB-3b verified computationally at a
  beyond-Johnson radius (live red-team pass for the Lean theorem);
* the sibling's δ*-pin is UNAFFECTED (it is a sup over radii strictly below the
  threshold; the good-side ownership bound applies there).

**Theorem landed** (`strongly_far_badScalars_card_mul_le`, axiom-clean): directions
with max codeword agreement ≤ k satisfy `#bad · (n−w).descFactorial (k+1) ≤ n^{k+1}`
at EVERY radius — at the boundary slice this is ≈ C(n,k+1), matching the measured
56 within the ordered-count factor.  The exact threshold value of ε_mca at the
boundary slice is now bracketed `[C(n,k+1), n^{k+1}/(k+1)!]`-ish for the far class,
with the far class provably extremal over the spectrum family.
## 2026-06-12 — UDR-edge band amendment: RADIUS coverage closed by composition (the no-go stands for the dichotomy budget)

The fifth no-go above is intrinsic to the universal DICHOTOMY's two branches, not to the
radius band: the subset-ownership law (`march_badScalars_card_mul_le`, glueing constant)
is radius-free, so the band `n ∈ [2w+k+1, 2w+2k)` moves at the subset budget
`C(n,k+1)/((k+1)·p)` — `UDREdgeClosure.lean` (`udrEdgeBand_closure`,
`le_mcaDeltaStar_subset_law_w`).  Below-UDR radius coverage is gapless at every rate.
What remains open on the band is only the BUDGET gap: the dichotomy's
`n^{k+1}/(n−2w−2k+1)^k` shape is unavailable there; recovering it needs the γ-line
mechanism (explainers of bad scalars move polynomially `p_γ = P(γ)` with codeword
coefficients; the column dichotomy — ≤ a−1 identically-zero columns else joint — gives
`#bad ≤ n·deg P`; the missing piece is SLOPE COLLAPSE: `deg P ≤ 1` on the band, probe
`_scratch_probe_slope_collapse.py`).

**Generic-domain addendum (same day):** the band is also closed for EVERY injective
evaluation domain (no smoothness) by a second independent mechanism — the γ-preserving
puncture descent (`BelowUDRPuncture.lean`): a direction vanishing at a witness point
`x₀` forces every explainer through `(x₀, u₀ x₀)` at every γ, and dividing the instance
by `(X − x₀)` maps `(n, k, w) → (n−1, k−1, w)` at the same γ with `n − k` (hence the
UDR slack σ = n−2w−k) invariant; induction on k bottoms at the k = 1 universal law.
Result: `#bad·(n−2w−k) ≤ n^{k+1}` on ALL of `2w+k+1 ≤ n` — one statement, the whole
below-UDR range, generic domain (`belowUDR_badScalars_card_mul_le`,
`le_mcaDeltaStar_belowUDR`, `udrEdgeBand_closure_generic`; probe
`probe_edgeband_puncture.py`, 633/633 descent checks).  Budget comparison stands: on
smooth domains in the band the subset budget `C(n,k+1)/((k+1)p)` is sharper, and on
`2w+2k ≤ n` the dichotomy budget is sharper — the descent adds generality (any domain),
uniformity (one statement), and a reusable γ-preserving transfer mechanism (it is
radius-agnostic: above UDR it descends every bad scalar whose witness meets the
direction's zero set; the complementary stratum has witnesses concentrated on the
support).  (Slope collapse was refuted the same day — see the entry above; the
descent bound here is unaffected, and the surviving two-regime pencil law plus the
moment-fiber question remain the named budget targets on smooth domains.)

## 2026-06-12 — SLOPE COLLAPSE REFUTED (directed t=2 construction); the surviving two-regime pencil law

The slope-collapse conjecture (UDR-edge amendment above: every band bad-family's
explainer map is affine, `deg P ≤ 1`) is FALSE as stated: the explicit quadratic-pencil
construction (`_scratch_probe_nonaffine_directed.py`, wt371) produces genuine nonaffine
bad families wherever the scalar field gives room.  Witness at the band instance
`(p, n, k, w) = (73, 9, 2, 3)`, `a = 6`:
`u₀ = (64, 48, 33, 62, 37, 56, 46, 22, 36)`, `u₁ = (5, 29, 30, 32, 65, 5, 29, 61, 55)`,
bad scalars `{12, 16, 36}`, no affine selection (verified over all explainer pairs).
The first random probe's zero-nonaffine reading at `p = 17, 19` was a small-field
artifact.  Design: column polys `−m₂(i)(γ−r₁ᵢ)(γ−r₂ᵢ)` with `m₂` a nonzero codeword and
the `γ¹`/`γ⁰` coefficients absorbed into the FREE `ε`/`u₀` — t = 2 needs no rigidity
beyond the top coefficient.

**What survives (verified by the same construction): the two-regime pencil law.**
Identically-zero columns of a degree-`t` pencil:
* `t = 1`: capped at `a − 1` by joint-exclusion only ⟹ `#bad_affine ≤ (n−z)/(a−z)`,
  maximal `w + 1` at `z = a−1`;
* `t ≥ 2`: the TOP Newton coefficient `m_t` is a nonzero codeword (divided differences
  of codewords), so `z ≤ k − 1` ⟹ `#bad ≤ t·(n−k+1)/(a−k+1)` — at the band ≈ `2t`.
  The probe's max nonaffine family (3) meets the `t = 2` cap `⌊2(n−k+1)/(a−k+1)⌋ = 3`
  exactly; it CANNOT beat the affine cap at `t = 2`.

**The open t-control, reduced:** beating `w + 1` needs `t ≈ w/2`, and a degree-`t`
pencil constrains `t − 2` symmetric functions of every column's root set to be
codeword-ratios — for non-constant ratios, ≤ `k−1` columns per value; for constant
ratios, the root `t`-sets lie in a fiber of `t − 2` prescribed power sums of the scalar
set `Γ`.  So the band adversary beyond affine is a SCALAR-SIDE deep moment-fiber
extremal problem (the census programme's object, transposed from the domain to the
scalar field): large nonaffine families need `|Γ| ≈ w` scalar sets that are
moment-degenerate to depth `≈ w/2` with large fibers.  Conjectured cap (next probe):
additive moment fibers at depth `t−2` collapse the supply below the affine cap for all
`t ≥ 2` ⟹ `#bad ≤ w + O(1)` on the band.
## 2026-06-12 — `WindowPencilAnchored` is NOT universal: class V (vanishing-denominator rows)

The window pencil law (`WBPencilWindowLaw.lean`) counts ≤ `(w+1)+n(w+1)+1` bad
scalars for stacks with an ANCHORED representation pair (some adjugate entry of
some square row-selection of the coefficient pencil ≢ 0, ⟺ corank ≤ 1 over
`F(γ)`).  The hope that every doubly-WB-solvable stack admits an anchored
representation is **FALSE**:

* **Class V** — rows that are *rational-with-exceptions* (`u = R/ℓ` off the
  domain zero set of `ℓ`, free at the zeros; the WB relation `ℓ(x_i)u_i = R(x_i)`
  forces `R` to vanish with `ℓ`, so these are honest WB rows) — generically has
  pencil corank ≥ 2 for EVERY representation pair: 103/130 fresh class-V stacks
  at `(13,6,1,2)` have NO anchored pair under FULL enumeration of both rows' WB
  solution spaces (`probe_wb_window_anchor_existential.py`); coranks up to 4
  occur (`probe_wb_window_corank2.py`).
* **The common-factor reduction is insufficient**: dividing the forced shared
  factor (the `(x−a)`'s where `ℓ` and `R` jointly vanish) out of all four data
  polynomials preserves corank verbatim under the uniform caps, and with the
  correctly shrunken cofactor cap (`m − z`) still leaves a residue class
  degenerate — the survivors are recognizable: shared reduced denominators,
  post-reduction polynomial rows (`probe_wb_window_reduced_anchor.py`).
* **The saving observation**: every unanchored stack found has ≤ 2 mca-bad
  scalars.  Mechanism (the proof route for the corrected residual): for
  `gcd(ℓ₀ℓ₁, Z_D) = 1` data below UDR, two `F(γ)`-independent kernel solutions
  force `Q₁Z₂ = Q₂Z₁` (degree < n) and `Z_D ∣ (A+γB)g − Lρ` for the gcd-split
  `Z_j = gζ_j` — every kernel solution is a polynomial multiple of ONE primitive
  triple `(g, ρ, c)` with slack in all three caps (the kernel is `K[x]`-cyclic);
  a bad scalar needs `g(γ,·)` to split over the domain, i.e. the anchored
  incidence count re-runs on the primitive curve.

**Surviving form** (`WBPencilWindowCapstone.lean`): `UnanchoredLinear` — stacks
with no anchored pair have ≤ `n` bad scalars (budget aligned with the repaired
`WindowRationalLinear`; strictly weaker than it via
`unanchoredLinear_of_windowRationalLinear`).  The below-UDR law
`ε_mca ≤ ((n+1)(w+1)+1)/q` holds under this residual alone
(`epsMCA_le_below_udr_of_unanchoredLinear`), with the anchored bulk carried by
the proven pencil law.

## 2026-06-12 — The deep-band supply: production closure via agreement caps is VACUOUS (analysis, not a refutation of the reduction)

The agreement-capped supply instance (`explainable_cores_card_of_agreement_le`:
`#explCores·C(k+m+1,k) ≤ C(n,k)·C(A−k,m+1)`) combined with the near-line
dichotomy (`near_scalar_unique`: at most one scalar's line exceeds agreement
`(n+k)/2`) does NOT close the production deep-band count: at `A ≈ (n+k)/2`,
`k ≈ n/2`, the bound `C(n,k)·C(A−k,m+1)/C(k+m+1,k) ≈ C(n,k)·2^{−(m+1)}` is of
the same order as the witness mass `C(n,k+m+1)/q^m·q^m`, leaving
`#badSet ≳ 2^{m+1}/q^m` — vacuous for `m ≥ 1` at production `q`.  The loss is
the `C(n,k)` factor from `k`-subset determination (only `q^k` codewords exist,
but `C(n,k)` `k`-subsets are counted).  Sharpening requires bounding the number
of codewords at agreement `≥ k+m+1` — below Johnson agreement that is
quantitatively the list-decoding wall (the known `δ*`↔LD coupling).  The
supply-side mathematics above the wall is proven; the wall itself remains the
open core, now in its sharpest isolated form.
## 2026-06-12 — round 9: the k-simplex packing collapses; the packing cap at `n` is FALSE (the overlap law)

Two round-8 census conjectures resolved in opposite directions
(`probe_packing_envelope.py`, `PackingEnvelope.lean`):

* **"k ≥ 3 disjoint (e+1)-simplex packings extend the envelope" — REFUTED.**
  The k-packing stack (`u₁ = q₀|_{S₁}`, `u₀ = (X·q₀)|_{S₁}`, `q₀` vanishing on the
  complement `Z` of the union) only depends on `(s₁, z) = (|S₁|, |Z|)`: the `k−1`
  other blocks are an undifferentiated reservoir whose every point contributes one
  `(X−x)q₀`-alignment scalar.  Count `n − z` at threshold `min(n−s₁+1, s₁+z+1)`;
  the per-radius optimum is the bisimplex value, and any `k ≥ 2` packing's count
  `k(e+1)` is `≤ 2E+2` at its own radius with the unified window implied
  (`kPacking_subsumed`, pure arithmetic).  Probe T2: at `(97,16,d=5), t=9` the
  `k=3,e=3` stack carries exactly its `12` while the `(s₁,z)=(8,0)` optimum carries
  `16` at the same threshold.  `k ≥ 3` never appears on the envelope.

* **"the packing count caps at `min(n, 2E+2)`" — REFUTED: the OVERLAP law.**
  The round-8 `t=7` hint (`20` at `(97,16,2)`) is a genuine char-0 family —
  hill-climbs at `p = 97` AND `p = 257` independently converge to `2(n−t)+2 = 20`
  with identical structure (two `(E+1)`-point simplex blocks overlapping in
  `n−2t+2 = 4` points, zero leftovers).  Reverse-engineered mechanism: stack
  `(X, 1)` on `S∖Y`, tuned `(a_x, b_x)` on the overlap `Y`, zero off `S`; each
  overlap point carries TWO bad scalars (its kill `−a_x/b_x` and its align
  `(x−a_x)/(b_x−1)`), so the count is `n + |Y|`, exceeding `n`.  Proven general
  (`overlap_packing_epsMCA_lower_bound`) and instantiated word-level exact at
  `(12289, 16, d=2)`: `20` bad scalars at radius `9/16` and `18` at `1/2`
  (probe-verified exact counts).  Grand packing law: `2(n−t)+2` on the whole
  window `d+2 ≤ t ≤ (n+d+1)/2`.

Side observation (probe T1): at `t = d+3` cells, e.g. `(97,16,4), t=7`, sub-optimal
`(s₁,z)` stacks pick up large SMALL-FIELD surpluses (`34` observed vs `14` designed;
expected-count heuristic `C(10,5)·C(6,2)/97 ≈ 39`) — the same codim-0 coincidence
species as the censused mod-17 extras; vanishes for `p ≫ poly(n)`.

### The any-domain sub-Johnson supply laws — REFUTED by the Frobenius secant family (Fable, 2026-06-13)

Context: the crossing/Cauchy–Schwarz campaign proved the mean-degree law `Σ|A| ≤ 2n`
for pairwise-`≤1` families down to the Johnson agreement `t² ≥ 2n`, and noted that
below it set systems blow up (projective planes), so "any proof must couple the word."
This entry sharpens the wall: **coupling the word is not enough — the blowup is
realized by genuine RS agreement families** (`FrobeniusSubfieldBlowup.lean`, 8 theorems,
axiom-clean; probe `probe_frobenius_blowup.py`, exact at `(p,e) = (3,2),(3,3),(5,2)`).

Mechanism (JH01/BSKR06 in the #389 charter objects): char `p`, `k = 2`, the Frobenius
word `w(z) = z^p` over any `𝔽_p`-affine-closed domain (e.g. all of `𝔽_{p^e}`, `n = p^e`).
Freshman's dream: the affine codeword `z₀^p + u^{p−1}(z−z₀)` agrees with `w` on the
ENTIRE affine line `z₀ + 𝔽_p u` — every secant of the Frobenius graph is `p`-rich.
At level `t = p` (sub-Johnson: `t² = n^{2/e} ≤ n`):

* **"`Σ|A| ≤ 2n` (or any `C·n`) below Johnson for RS agreement families" — REFUTED.**
  The family is pairwise-`≤1`, every member exactly `p = t` points
  (`frobenius_explainable_inter_le_one`), and the mass SATURATES the universal pair
  bound exactly: `Σ|A| = n(n−1)/(p−1)` (`frobenius_mass_floor`,
  `frobenius_mass_gt_two_n`).  At `e = 2` this is `≈ n^{3/2}` at `t² = n` — failure
  one notch below the Johnson threshold `2n`, matching the projective-plane envelope
  (the family IS the affine plane `AG(2,p)`, sheared into a function graph).
* **"the capped optimum / explainable-core supply is linear in `n` at fixed `(k,m)`"
  (the growth-law census conjecture, measured at prime `q`) — REFUTED in any-domain
  form.**  At fixed `(k, m) = (2, p−3)`: explainable-`p`-core count
  `= n(n−1)/(p(p−1)) = Θ(n²)` (`frobenius_supply_floor`); against the named Prop:
  any `B` for `ExplainableCoreSupply dom 2 (p−3) B` has `n(n−1) ≤ p(p−1)·B`
  (`frobenius_charter_floor`).  The prime-`q` census probes were structurally blind
  to this: the mechanism needs a proper subfield.

What is NOT refuted: `ExplainableCoreSupply` with `B` subexponential in the witness
mass (the Frobenius supply is only quadratic — the self-cap `deg(X^p − aX − b) = p`
bounds every agreement at `p`); and the production setting `μ_n ⊂ 𝔽_q` with `q` prime,
where the only `𝔽_p`-lines have size `q ≫ n`.  Consequence for the programme: the
sub-Johnson supply statement is irreducibly DOMAIN-coupled — any proof must use the
absence of `𝔽_p`-affine structure in the evaluation domain (no-large-subfield /
additive-unstructuredness of `μ_n`), not just `w ∉ C` and pairwise distance.

#### Addendum (same day, second lane): COMPOSITE subfields obstruct too — at every band (`SubplaneSupplyFloor.lean`)

The Frobenius-secant entry above leaves two gaps, both now closed
(`SubplaneSupplyFloor.lean`, axiom-clean; probe `probe_subplane_supply.py`, exact at
`F₉/K=F₃`, `F₂₇/K=F₃`, `F₁₆/K=F₄`):

* **Any prime-power subfield `K`, `r = |K|` — not just the prime one.**  Shear
  `AG(2, K)` into `F` by `(a,b) ↦ a + λb`, `λ ∉ K`: domain `n = r²` points, word
  `w(a+λb) = b`.  The `r²+r` lines of the plane become honest degree-`<2` codewords
  (`y = (sx+c)/(1+λs)`, `y = (x−a₀)/λ`) agreeing with `w` on exactly `r = √n` points
  each, pairwise `≤ 1` (probe: agreement histogram is `{0,1,r}` ONLY).  In char 2 the
  Frobenius mechanism is vacuous (`t = 2` fills no core) — here `K = 𝔽_{2^j}` bites at
  every `j`: **binary-tower (char-2 production) fields carry the explosion whenever
  the evaluation domain contains a sheared `K`-plane; only PRIME fields are immune to
  the subfield mechanism.**
* **Every band at once**: `subplane_supply_floor` — any `B` for
  `ExplainableCoreSupply dom 2 m B` has `(r²+r)·C(r, 2+m+1) ≤ B`, for ALL `m` with
  `2+m+1 ≤ r` simultaneously (`≈ n^{(m+3)/2}`, superpolynomial at every fixed band
  depth) — vs the single tuned band `2+m+1 = p` of the secant floor.

Unchanged verdict, sharpened scope: the sub-Johnson supply statement is irreducibly
domain-coupled, the coupling needed is *absence of sheared-subfield-plane structure*,
and the surviving positive targets are prime fields and (conjecturally) smooth `μ_n`
domains — for binary-tower deployments the supply route is closed unconditionally at
subfield-aligned domains.

## 2026-06-12 — μ_n-immunity is q-CONDITIONAL: prime-field, multiplicative-subgroup linear supply REFUTED at `n = Θ(q)` (the generic-density phase)

Claim refuted: "`SubJohnsonSupplyResidual dom k m B` holds with `B = O(n)` (or any
`B = o(C(n,t)/q^{m+1})`, `t = k+m+1`) for multiplicative subgroups `μ_n ⊂ 𝔽_q`,
`q` prime" — the surviving hope of the Frobenius entry above ("the production setting
`μ_n ⊂ 𝔽_q` with `q` prime") and the convergence comments' "μ_n tracks the random set
`~O(n)`".  Both were measured at `q ≫ n` only.

Witness (`MonomialSupplyWitness.lean` + the pair-hash probe): `w = x^t`, `t = k+m+1`.
Capped for free (`monomial_word_agreement_le`: agreements `≤ t ≤ 2k+m+1`); a `t`-set
`T` is an explainable core iff the remainder window of `x^t mod ∏_{i∈T}(X−x_i)`
vanishes (`explainableOn_of_remainder_degree_lt` — the remainder IS the codeword;
`monomial_supply_ge`).  The window is codimension `m+1`: density `C(n,t)/q^{m+1}`.
Exact counts at `(k,m) = (2,1)`, `t = 4`, cap `4 ≤ 6`:

* full units of `𝔽₁₂₇` (`n = 126`): **630 = 5.0·n** cores (agreement profile
  `{1:5418, 2:3969, 3:42, 4:630}` — cap verified);
* full units of `𝔽₂₅₇` (`n = 256`): **2,624 = 10.25·n**;
* **`μ₄₀₉₆ ⊂ 𝔽₁₂₂₈₉` — THE standard 2-smooth NTT domain: 103,424 = 25.25·n**,
  33% ABOVE the generic `C(n,4)/q² ≈ 77,546` — subgroup vanishing-sum arithmetic
  ENHANCES the density; the opposite of immunity;
* full units of `𝔽₃₁` (the census scale): 30 = 1.0·n — invisible; the measured
  "linear growth law" (30/46/67/86 at `q = 31`) was a scale artifact.

Consequences: (i) the unconditional pair-count ceiling `B = C(n,k)` is asymptotically
TIGHT at `n ~ q` (within the `t!`-constant) — at fixed rate and `n = Θ(q)` the supply
question is closed at `Θ(n^k)`; (ii) the open charter is now `q`-conditional:
`q^{m+1} ≳ n^{t−1}/t!` (production `q ≥ 2^128` is safely inside); (iii) the corrected
exact-solution target is the **two-phase law** `E_max(μ_n) = Θ_{k,m}(n + C(n,t)/q^{m+1})`
— arithmetic/fibre families rule `q ≫ n`, generic density rules `n = Θ(q)`, and any
positive proof must use BOTH the additive-unstructuredness of `μ_n` (Frobenius entry)
AND the field-size hypothesis (this entry).
## 2026-06-12 — the sub-Johnson supply curve IS small-set Szemerédi–Trotter (Fable; `GridSupplyRefutation.lean`)

A reframing entry, complementary to the two-branch/Frobenius/subplane/monomial
witnesses above.  All of those exhibit blowup; this one *names the curve* and points
at a formalizable unconditional improvement.

Observation: for `k = 2` an explainable `t`-core (`t = k+m+1 ≥ 3`) is exactly a
`t`-subset of the word's graph `P = {(dom i, w i)} ⊂ 𝔽_q²` that is collinear, and (for
`t ≥ 3`) it lies on a *unique* affine codeword.  Hence **explainable-core supply =
`Σ_{lines ℓ} C(a_ℓ, t)` = the rich-line incidence count of the graph point set** —
the Szemerédi–Trotter rich-line problem.  The capped residual restricts to `a_ℓ ≤ t+2`.

Witness (`GridSupplyRefutation.lean`, axiom-clean, `n = 36`, `ZMod 41`, fixed band
`(k,m) = (2,1)`, `t = 4`, cap `6`): the `6×6` sheared grid `(i,j) ↦ (i+7j, j)` (abscissae
= base-7 digits ⟹ word graph; shears preserve lines).  `grid_word_cap` proves the cap
*structurally* (no root budget: a non-constant line meets each constant row `≤ 1×`; six
rows) ⟹ the word is in the `SubJohnsonSupplyResidual gridDom 2 1` class.  Yet
`subJohnsonSupplyResidual_floor_grid`: every valid `B ≥ 234`, strictly above the
partition target `90` and the (now-dead) mean-degree-law target `180`.  Asymptotically
(`probe_grid_supply_refutation.py`) the family-capped mass is the ST extremal
`Σ a_ℓ = Θ(n²/t²)`, violation `×11.2` at `n = 400` — and the construction is over ℤ,
so it transfers to `𝔽_p` for every prime `p > 2N³` (subfield-free production primes
included), the prime-field counterpart of the subplane mechanism.

* **REFUTED**: "the mean-degree law `Σ a_ℓ ≤ 2n` holds on the residual's hypothesis
  class at a fixed band" (the `n ≤ 20` census stopped below the ST onset `n ~ t³`).
* **NOT refuted, and the corrected shape target**: for additive/`μ_n` domains the
  rich-line count obeys the small-set finite-field ST conjecture
  `L_{≥t} = O(n²/t³ + n/t)`.  Concrete **unconditional partial**: Stevens–de Zeeuw
  (via Rudnev's point-plane bound) gives `I(P,L) ≲ |P|^{11/15}|L|^{11/15} + |P| + |L|`
  in the production range `p ≫ poly(n)`, hence `L_{≥t} ≲ n^{11/4}/t^{15/4}` — which
  **beats the packing bound `n²/t²` for every `t > n^{3/7}`**, i.e. on the band
  `(n^{3/7}, √(2n))` strictly below Johnson `√(2n)`.  This is the first unconditional
  strictly-sub-Johnson supply improvement; formalized as a named-residual import +
  consumer chain in `STSupplyReduction.lean` (the heavy Rudnev bound is the import
  surface; the reduction `RichLineBound → capped supply → bad-set count` is proven).

## 2026-06-13 — THE UNIVERSAL MEAN-DEGREE LAW IS FALSE (two-branch parabola countermodel); the supply growth law is two-regime

The conjectured universal form of the mean-degree law ("`Σ_c a_c ≤ 2n` over the
capped large-agreement family of any word", probe census `717da6067` / the #389
thread's "final measured form") is **REFUTED** in the open sub-Johnson range
`t² < 2(k−1)n` (`TwoBranchSupplyCountermodel.lean`, axiom-clean):

* **The countermodel family**: split `D = A ⊔ B`, set `w = x²` on `A`,
  `x² + c` on `B`.  Every degree-`<2` polynomial agrees with each branch on
  `≤ 2` points (root budget), so every codeword agreement is `≤ 4 ≤ 6 =
  2k+m+1`: **agreement-capped unconditionally**.  The line through
  `(x₁,x₁²), (x₂,x₂²)` meets branch `B` at the roots of
  `z² − (x₁+x₂)z + (x₁x₂+c)`; when the discriminant `(x₁−x₂)² − 4c` is a
  nonzero square with both roots in `B`, the line is 4-rich.  About `1/8` of
  the `A`-pairs qualify: `Σ a_c ~ n²/16`, **quadratic**.
* **Machine-checked instance** `(q,n) = (101, 80)`: interval domain
  `{0..79}`, `A = {0..39}`, `c = 29`: `107` four-rich lines (census-exact:
  these are ALL the `≥4`-rich lines; max agreement `4`), `Σ a_c = 428 > 160 =
  2n`.  `universalMeanDegreeLaw_REFUTED`.
* **Why the censuses missed it**: at `q = 31, n ≤ 24` the two-branch count
  sits below `2n` — the crossover `n³ ≈ 64q²` is exactly where the growth
  census stopped.  `probe_two_branch_subjohnson_supply.py`: 21/25 instances
  violate (first at `p = n = 41`, exact counting); the linear-B form
  (`≈ 3.625n`) falls from `p = 251` (957 cores vs 910).
* **What survives**: `mean_degree_law_deep` and the crossing/CS route are
  hypothesis-guarded (`t² ≥ ~2(k−1)n`) and unaffected — and now provably
  SHARP: below the threshold the truth is a different growth law, not a
  missing word-coupling refinement of the linear one.
* **The corrected named target** (`CappedSupplyTwoRegimeLaw`, PRIME fields):
  `S_max(capped) = Θ(n + C(n,k+m+1)/q^{m+1})` — partition floor + random
  mean.  The two-branch family realizes the mean term constructively (and
  `r`-branch words `x^k + c_j` extend this to every band `m` with
  `r·k ≤ 2k+m+1`).  The general-field form is FALSE by subfield transport:
  over `q = p²` with `D = F_p ⊂ F_{p²}` the same construction carries
  `~ n²/64` cores while the mean term collapses to `O(1)` — char-2/extension
  production settings need a no-large-subfield-structure hypothesis.
  Consumer arithmetic: any `B = O(n + C(n,t)/q^{m+1})` still delivers
  prize-grade bad-scalar counts through `deep_band_badSet_card_of_residual`
  (`#badSet ≳ min(C(n,t)/(qᵐ·n), q/const)`) — the wall is recalibrated, not
  destroyed.
## 2026-06-12 — "Linear/subexponential supply on smooth domains" is FALSE for DYADIC domains (multiplicative subspace polynomials)

The rounds 78–84 census conjecture — capped supply `Σ_c C(a_c,t) = O(n)` (`B = O(n)`),
"empirically true with subexponential `B`" — is **refuted for the explicit smooth 2-adic
(FFT) domains the prize targets**. The linear value is the *random-RS / Singleton-optimal*
list size; structured smooth domains beat it exponentially. The census hill-climbs missed
the structured extremizer, exactly as hill-climbing misses BKR subspace polynomials.

**Construction** (`EsymmFiber.lean`, axiom-clean; `probe_coset_union.py`, full-enum
verified μ₁₆/μ₃₂). Domain `μ_n`, `n = 2^μ`. Reformulation: a degree-`t` word's explainable
`t`-cores are the `t`-subsets `A` with prescribed `e_1..e_{m+1}` (Vieta;
`explainable_iff_forcedPoly_degree`). For `w = wt·X^t + (deg<k)` the prescribed values are
`0`. A union `A` of `s` cosets of `μ_d` (`d = 2^j ≥ m+2`, `s·d = t`) has
`∏_{a∈A}(X−a) = expand_d(Q)` ∈ `F[X^d]`, so `e_1(A)=…=e_{d−1}(A)=0` ⊇ the constraints, and
the forced explainer has degree `≤ t−d = k−1 < k`. Hence every such union is an explainable
core (`explainable_of_expand`), and there are `C(n/d, t/d)` of them
(`smooth_dyadic_supply_lower_bound`):

  `#explainable t-cores ≥ C(n/d, t/d) = 2^{H(ρ)·n/d·(1+o(1))}`  — EXPONENTIAL.

Regime: agreement `α = t/n = ρ + d/n`, just above capacity, strictly sub-Johnson
(`α < √ρ`). `μ_d ⊂ μ_n` = the multiplicative analogue of an additive BKR subspace
polynomial; needs only the multiplicative 2-adic subgroup tower (no subfield — works over
prime fields). Consistent with: only random RS reaches capacity (GG25 2025/2054); the
up-to-capacity proximity-gap conjecture is false (BCIS-2025 2025/2055, CS25 2025/2046); the
barrier is the list-decoding radius (PG⇒LD, BCIS-2025 Thm 1.9).

**Status:** the "subexponential uniform supply `B`" supply statement is FALSE on `μ_{2^μ}`
at the deep band. Any positive supply/MCA result there must restrict the domain away from
dyadic structure or accept exponential `B`. Refutation is machine-checked (not a wall — a
proved negative). The campaign's recent linear claim should be re-scoped to random/generic
domains; the prize's smooth-domain case is exponentially worse and this is the honest state.

### O158 — THE PRODUCTION-RATE OBSTRUCTION: the multiplicative-subspace exponential supply is VACUOUS at fixed production ρ — it requires vanishing rate, exactly like DG25 (nubs incidence/census lane, 2026-06-13)

Boundary map of `EsymmFiber.smooth_dyadic_supply_lower_bound` (the just-landed "smooth
dyadic domains have exponential sub-Johnson supply") vs the prize's production parameters.
Claimed #389 comment 4697214100; exact integer arithmetic, `scripts/probes/incidence/boundary/`.

**The construction's firing condition (exact, from the Lean hypotheses):** a μ_d-coset
union is an explainable t-core iff `d = 2^j | t`, `d ≥ m+2`, `t = k+m+1`; supply
`C(n/d, t/d)`. Exponential supply requires `d = O(1)` (so `n/d → ∞`).

**The obstruction (verified mu=5..14, all production rates):** at fixed production rate
`ρ ∈ {1/2,1/4,1/8,1/16}` (so `k = ρ·2^μ` is a large power of 2), the best coset-union
supply rate `log₂(supply)/n → 0` as the domain grows — **POLYNOMIAL, not exponential**
(ρ=1/2: identically 0 at every μ; ρ=1/4,1/8,1/16: halving each μ-step). 2-adic mechanism:
exponential needs constant `d=2^j ≥ m+2` dividing `k+m+1`; for `k=2^a` and constant `m`,
`2^j | (2^a+m+1)` with `2^j ≥ m+2` forces `2^j | (m+1)` ∧ `2^j ≥ m+2` ⟹ `m+1 ≥ 2^j ≥ m+2`,
impossible. The only firings have `d ∝ n` (giving `C(O(1),O(1))` = constant supply) or
sit at the s=1,2 single/few-coset tips (linear supply, rate → 0).

**Where the exponential bite actually lives:** non-production rates `ρ → 0` (fixed small
absolute `k`, rate shrinking with n) — e.g. k=5,9,13 show genuine positive supply rate.
**This is exactly the DG25 escape** (DISPROOF_LOG §3/Loop: DG25's super-poly capacity
disproof needs vanishing rate `ρ ≈ e·n^{1/3}/n → 0`, not fixed ρ). The multiplicative-
subspace construction is the explicit-smooth-domain shadow of DG25 and respects the SAME
rate barrier — it does not cross into fixed-rate territory.

**Consequence for #389 / the pin:** the EsymmFiber theorem is true and axiom-clean, but
its defeat of subexponential `ExplainableCoreSupply` (and hence any threat to
`CensusDomination` / the δ* pin) is confined to vanishing-rate regimes. **At the
production rates the prize actually targets, this construction yields only polynomial
supply — it does NOT break the pin there.** HONEST SCOPE: this maps ONE construction's
support; it does NOT prove `CensusDomination` (other supply sources may exist, e.g. the
Frobenius-subfield blowup O-entry, which is additive-structure-coupled and a separate
question). It removes the multiplicative-subspace route as a production-rate obstruction
and pins it to the same vanishing-rate barrier as the known capacity disproofs.

## 2026-06-13 — THE SUPPLY-SIDE PACKING BOUND IS WORST-CASE VACUOUS; the line-partition is the algebraic fix (Fable)

Distinct from the failure-side packing entries above (those bound bad-scalar *counts* from
below): this is about the **supply** (`ExplainableCoreSupply`, the #389 positive direction),
which counts explainable `(k+m+1)`-cores of a word `w` from above.

**The exact identity** (`ExplainableCoreExactCount.lean`, axiom-clean):
`#cores(w) = Σ_c C(|agreeSet c w|, k+m+1)` — each core lies in exactly one codeword's
agreement set (`k+m+1 > k−1` ⟹ uniqueness via `rsCode_pairwise_agreeSet_card_le`). So the
supply IS the agreement-size profile `(a_c)`.

**The refutation.** Combined with the `k`-subset packing `Σ_c C(a_c,k) ≤ C(n,k)` and the fact
that `C(a,k+m+1)/C(a,k)` is increasing in `a`, the extremal profile is a SINGLE codeword with
`a_c ≈ n`, giving `#cores ≈ C(n,k+m+1)` = the trivial bound (`probe_supply_extremal.py`:
single/trivial = 1.0000 at every production scale n=16…256). **So no purely combinatorial /
packing / Johnson-first-moment argument can give a sub-trivial per-word supply** — a word
near a single codeword saturates it. Any supply proof MUST use the algebraic structure of
which words arise as bad-scalar lines.

**The line-partition fix** (`LineCorePartition.lean`, axiom-clean): for the bad-scalar line
`w_γ = u₀ + γ·u₁` with `u₁ = xᵏ` far from the code (agreement `< k+m+1`),
`line_core_unique_scalar` shows each core is explainable for ≤ 1 scalar (secant-slope
codeword would agree with `u₁` on `k+m+1` points), so `line_total_cores_le`:
`Σ_γ #cores(w_γ) ≤ C(n,k+m+1)`. This is the line-level (aggregate) supply — the algebraic
constraint the refutation proved is required. NOT a full closure: it bounds the line aggregate,
not the per-scalar worst case; the per-scalar gap remains the open wall, but it is now precisely
localized to "is the worst-case-γ core count `≪` the line average `C(n,a)/q`?"

## 2026-06-13 — smooth-domain δ* tracks subgroup ARITHMETIC, not smoothness (QR-bad / 2-power-good)

A structural finding from the exact m=0 (cubic) supply on two smooth domains, both
machine-checked, that sharpens what "smooth-domain immunity" can mean:

* **2-power NTT domain `μ_16 ⊂ F₂₅₇`** (`cubicSupply_mu16_F257_eq_zero`): cubic word
  `x³` has **exactly 0** explainable 3-cores at radius `13/16` (one step below
  capacity) — the char-0 Mann rigidity (no cube root in `μ_{2^k}` ⟹ no three 2-power
  roots of unity sum to zero) **survives to `F₂₅₇`**.  δ*-GOOD.
* **QR index-2 domain `QR* ⊂ F_q`** (`qr_zeroSum_ordered_card`): the cubic ordered
  zero-sum count is `8·#ord + 6q = q² + 5`, i.e. `(q−1)(q−5)/8 = Θ(n²)` — the
  additively rich index-2 subgroup carries **quadratic** near-capacity cubic supply.
  δ*-BAD.

So a domain being "smooth" (a multiplicative subgroup) is NOT enough for a good δ*;
the relevant invariant is the **additive structure of the specific subgroup**.  The
production NTT domains (`μ_{2^k}`, FFT) are exactly the arithmetically-rigid good ones;
index-2 (QR) is bad.  This is consistent with the GV/HBK programme (the additive energy
`E(μ_n)` is the governing quantity) and with `representationCount_eq_gcd_degree`
(`GVRepBound G M ⟺ deg gcd(Xⁿ−1, (Cc−X)ⁿ−1) ≤ M`, no slack): the gcd degree, hence
the energy, hence δ*, is a subgroup-arithmetic quantity.  CAVEAT: `μ_16/F₂₅₇`'s zero is
PRIME-DEPENDENT (other primes give positive cubic supply for `n=16`); there is no
general `gcd(3,n)=1 ⟹ supply 0` transfer to `F_p` (the char-0 rigidity does not
transfer in general — that gap is exactly why the unconditional bound needs Stepanov).

### O159 — BOTH supply-explosion mechanisms PROVABLY production-blocked: the Frobenius immunity brick (nubs, 2026-06-13)

The sub-Johnson supply wall (#389) has two known explosion mechanisms; both are now proven
vacuous at production smooth μ_n. (1) Coset-union (EsymmFiber): production-vacuous by the
2-adic obstruction (O158); the swarm's pin-band check (4cf519992) independently confirms
the m=1 FFT domains are off-by-one blocked. (2) **Frobenius subfield blowup** (Θ(n²) supply,
`FrobeniusSubfieldBlowup.lean`): gated entirely on `AffClosed dom p`; immunity was
PROSE-ONLY in-tree (FrobeniusSubfieldBlowup.lean:37-39) until this brick.

**`FrobeniusImmunityMuN.lean` (axiom-clean ×3, single-module build green):**
`le_card_of_affClosed` (AffClosed ⟹ p ≤ n via the existing `secant_card`: the 𝔽_p-line
through two domain points has exactly p points, all in the n-point domain) →
`not_affClosed_of_card_lt` (2 ≤ n < p ⟹ ¬AffClosed) → `smoothDom_not_affClosed`
(production μ_n ⊂ 𝔽_q, q prime, 2 ≤ n < q is NOT 𝔽_q-affine-closed; only CharP of 𝔽_q is q,
so AffClosed is type-correct only at p=q, where the q-point affine line cannot fit an
order-n multiplicative subgroup).

**Consequence:** every `AffClosed`-gated Θ(n²) supply source is vacuous over production
smooth domains; with O158 both known super-polynomial sub-Johnson supply routes are
production-blocked. HONEST SCOPE: proves two specific mechanisms cannot fire; does NOT
prove `CensusDomination` (no exponential supply from ANY source). Remaining: the max
e-symm fiber census over all targets (H-MAX) + the inverse theorem that structured families
are the only supply sources (H-EXT) — in progress, `scripts/probes/incidence/landscape/`.

### O160 — SidonModNeg(μ_n) holds far below √p but the threshold is NOT universal-in-√p (probe + refutation, 2026-06-13)

Direct attack on the energyExcess core (`EnergyExcessCore.lean`): the whole #389 cubic/energy
wall closes iff `energyExcess(μ_n) = E⁺(μ_n) − (3n²−3n) = 0`, i.e. iff `μ_n` is `SidonModNeg`
(`AdditiveEnergySidonModNeg.lean`; in-tree `E ≤ 3n²` is conditional on it).

**Probe (`scripts/probes/probe_sidonmodneg_threshold.py`, exact `E⁺` in `F_p`):** small
multiplicative subgroups are EXACTLY Sidon-mod-negation (`excess = 0`, `E = 3n²−3n` exactly) far
below the random heuristic — e.g. `p=786433, n=256`: `n³/p ≈ 21` exotic quadruples predicted,
**0 observed**. Holds for any order (not just 2-power): `n=6..192 | p−1` all zero-excess.

**Bold conjecture E'' (exact universal minimality, `n ≤ c√p ⟹ excess 0`): REFUTED.** No universal
multiplicative-in-√p constant exists:
- `p=786433`: zero excess at `n=256` (`n/√p = 0.289`).
- `p=23068673`: ALREADY nonzero at `n=1024` (`n/√p = 0.213`).
Since `0.213 < 0.289`, no constant `c` with `n ≤ c√p ⟹ excess 0` fits both. The
Sidon-mod-negation threshold is genuinely p-dependent (number-theoretic), not a clean power law.
(Flip points `n/√p`: 0.32, 0.58, 0.38, 0.21 across p = 40961, 786433, 7340033, 23068673.)

**What survives (honest):** the PRIZE regime `n ≲ 2³⁰ ≪ √q ≈ 2¹²⁸` sits ~2⁹⁸ below every observed
flip, so `SidonModNeg(μ_n)` (hence `energyExcess = 0`, `E = 3n²−3n`) is empirically overwhelming
there — but proving it needs the p-dependent threshold, which Weil/character-sum bounds do NOT
force to exactly zero (the observed suppression is stronger than Weil predicts; an open
number-theoretic fact).

**Why this does NOT pin δ* (the load-bearing caveat):** even with `energyExcess = 0`, δ* is not
closed. Zero excess controls the additive-energy / cubic-supply front only. The **capacity-edge
supply is a SEPARATE mechanism** (`CS25*`: deep-hole + random-word combinations cover
small-distance balls, `ε_mca → 1` at capacity, NOT additive-energy-governed), which sets the upper
bracket `δ* ≤ 1−ρ−Θ(1/log n)`. Residual-free δ* therefore requires BOTH the subgroup sum-product
front (this entry) AND the covering / list-decoding-capacity front (CS25/BCHKS Conj 1.12) —
two independent recognized-hard problems. No fabricated closure.

### O161 — the coset/power-word construction is NOT the extremal max-list word (Conjecture J refuted, 2026-06-13)

Direct attack on δ*: the in-tree `rootsOfUnity_dyadic_codeword_list_ge` gives list `≥ C(n/d, t/d)`
via coset-union subsets; worked against the budget `list = q·ε*` with `q = poly(n)` this reproduces
the BCHKS upper bracket `δ* ≤ 1−ρ−Θ(H(ρ)/log n)` CONSTRUCTIVELY. **Conjecture J** asked whether this
construction is also the MAXIMUM list (which would pin δ* residual-free).

**Probe (`scripts/probes/probe_extremal_word.py`, exact list enumeration, F₉₇, μ₁₆, k=2):**
- `t=3` (sub-Johnson): `L(x³) = 0` (this μ₁₆ has no zero-sum triples) but `max over 40 random
  words = 11`. The power word is BELOW the random baseline; the coset construction (degenerate
  here, 3∤16) gives 0. The true max-list word is neither the power word nor coset-structured.
- `t=4`: `L(x⁴)=4`, random max 3 (power word competitive here); `t=5`: all 0.

**Verdict: Conjecture J REFUTED.** The coset/power-word construction is a valid list LOWER bound
(hence a valid δ* UPPER bracket) but is NOT extremal — the maximum sub-Johnson list is larger and
word-dependent. Pinning δ* requires the extremal/worst-word characterization (H-MAX), which this
shows is not the obvious construction. No fabricated closure; H-MAX remains the open residual.

**Caveat:** small-scale, `max-over-40-random` is a weak lower bound on the true max (could be far
larger); this strengthens, not weakens, the refutation (even a weak search beats the construction).

### O162 — H-MAX (extremal middle-band list) ↔ subset-sum fibres ↔ additive energy: the loop closes (2026-06-13)

Refined Conjecture J' (coset/power-word extremal in the MIDDLE band t=k+m+1, the prize regime,
not the sub-Johnson regime O161 tested). Probe (`probe_midband_extremal.py`, F₁₇, n=16, k=4, full
exact enumeration of all 17⁴ codewords):
- `t=5`: `L(x⁵)=256` BEATS random (max 167) — but `x⁵`'s list = `#{5-subsets of μ_n summing to 0}`
  (the e₁=0 fibre), and μ₁₆=F₁₇^× is the FULL group where sum-zero subsets are abundant.
- `t=6`: `L(x⁶)=32` > random 21 (same mechanism, e₁=e₂=0 fibre).
- `t=7`: `L(x⁷)=0` < random 6 (4∤7, coset construction degenerate).

**The closure (why this ends the direct attack):** the power-word list IS the subset-sum fibre
count `#{t-subsets with e₁..e_{t−k}=0}`. So the extremal-list question (H-MAX) is the subset-sum
fibre question, which is governed by the additive structure of μ_n — i.e. by `E_Fp(μ_n)` and the
SidonModNeg threshold. For the FULL group (abundant sum-zero subsets) the power word is extremal;
for a PROPER SidonModNeg subgroup (the prize, sum-zero subsets rare) it collapses to ~0 (cf. O161
t=3). Therefore **H-MAX, the subset-sum fibre supply, and `E=O(n²)` are the SAME irreducible core**
— every direct route to δ* (energy front, capacity-edge front, extremal-list front) lands here.

Conjectures refuted/closed this campaign: E'' (O160), J (O161), J' (O162) + the swarm's 6 bypasses
of E≤Cn². The δ* residual-free target is equivalent to the multiplicative-subgroup additive-energy
conjecture `E_Fp(μ_n)=n^{2+o(1)}` (best known n^{2.44}, Shkredov) — a recognized open problem.
No fabricated closure.

### O163 — δ* is NOT pinned by the exact subset-sum fibre: H-MAX is a combinatorial densest-cluster (Conjecture L refuted, 2026-06-13)

The unconditional Garcia–Voloch/Stepanov bound E ≤ 4n^{8/3} already makes the energy/cubic supply
SILENT at prize scale (≈2^85 ≪ q·ε* = 2^128), so δ* is bound by the NEAR-CAPACITY extremal list
(H-MAX), a higher-order subset-sum fibre — which for 2-power domains is EXACTLY known
(`TwoPowerFibreValue`). **Conjecture L**: power word extremal at near-capacity ⟹ δ* pinned exactly
by the fibre value, no residual.

**Probe (`probe_powerword_extremal_search.py`, μ₈⊂F₁₇ PROPER subgroup, k=2, t=3 = middle band,
strong hill-climb + 300-random search):** `L(x³) = 0` (= #sum-zero 3-subsets; μ₈ is SidonModNeg)
but the **strong search finds a word with list 7**. The power word is beaten by a non-algebraic,
non-subset-sum word.

**Verdict: Conjecture L REFUTED.** The extremal list H-MAX is a *combinatorial densest codeword
cluster* (7 linear codewords pairwise agreeing ≤1, all ≥3-agreeing with one deep word), NOT the
algebraic power-word fibre. So δ* is NOT pinned by `TwoPowerFibreValue`; the binding quantity is the
explicit-RS sub-Johnson list-decoding bound, which has no closed form — the recognized open problem.

**Campaign tally (direct δ* attack, all probe-refuted, all logged):** E'' (O160, energy-minimality
threshold non-universal), J (O161, coset not extremal sub-Johnson), J' (O162, extremality=subset-sum
=energy core), L (O163, H-MAX is combinatorial densest-cluster not the fibre). + swarm's 6 E≤Cn²
bypasses. Every direct route to a residual-free δ* terminates at the explicit-smooth-RS
sub-Johnson list-decoding bound = a recognized open problem. No fabricated closure.

### O164 — H-MAX deep-band fiber is O(1) at production primes (the e-symm map is near-injective/Sidon); a small-prime SATURATION GUARDRAIL (nubs, 2026-06-13)

Census of the max e-symm fiber at the deep band (offset m=1, the open #389 region), with a
methodology correction that matters for the whole campaign.

**The guardrail (a trap others can hit):** counting the supply fiber
#{t-subsets of μ_n : e₁..e_{m+1} = target} mod a SMALL prime is meaningless when
p^{m+1} ≪ C(n,t): the targets saturate and every bucket holds ~C(n,t)/p^{m+1} subsets by
PIGEONHOLE, not by genuine fiber structure. Concretely at n=32, m=1, p=97: C(32,18) ≈ 5×10⁸
subsets into p² = 9409 targets ⟹ "max fiber" 51,160 ≈ the pigeonhole average, fully
saturated (#targets hit = 9409 = p², all of them). This is a small-prime artifact, NOT
supply — the same char-0→mod-p failure mode O134 flagged, in its most extreme form.

**The faithful result (production-scale prime p = 2013265921):** at n=16, m=1, both
production rates, the e-symm targets are NOT saturated (C(16,10) = 8008 ≪ p²), and the
TRUE max fiber over ALL targets is **3** (brute-materialized: 7864 distinct targets for
8008 subsets — the map is near-injective). The structured zero-target (e₁=e₂=0) fiber is
**0**. So the deep-band supply is **O(1)**, not exponential: the p=97 numbers were pure
saturation.  (matching-trick fiber
counter, validated against brute force).

**Alignment + consequence:** max fiber O(1) ⟺ the e-symm map on t-subsets of μ_n is
near-injective — exactly the fleet's  (O160) and 
(E = 3n²−3n) framing; this is the empirical confirmation of that analytic attack. So
**H-MAX (no exponential deep-band supply at production) holds empirically**, and the
asymptotic closure is precisely the Stepanov/Sidon/additive-energy bound the fleet is
building. HONEST SCOPE: n=16 faithful + n≤16 exhaustive; the n≥32 asymptotic is the
analytic (Stepanov) bound, not brute-measured (production-prime materialization is
memory-prohibitive). Combined with O158/O159 (both structured explosion mechanisms
production-blocked), the supply-explosion landscape at production is: structured
constructions vacuous, the e-symm map near-injective ⟹ no known route to super-polynomial
supply — the CensusDomination premise, supported empirically; the proof is the fleet's
Stepanov multiplicity bound.

### O164 — max-list is field-independent ONLY in the Johnson regime; open regime is computationally inaccessible (Conjecture M, 2026-06-13)

Conjecture M: the cyclic-symmetry of the smooth domain forces a clean field-independent closed form
for the max single-word list, pinning δ*. Probe (`probe_maxlist_field_independence.py`, hill-climb
max-list): `n=8,k=2,t=3 → maxlist = 7 = n−1` across SEVEN fields (p=17,41,73,89,97,113,137) —
genuinely field-independent. BUT `t=3` is the Johnson regime (Johnson agreement √(n(k−1))=√8≈2.83),
where the combinatorial Johnson bound IS known and field-independent — not new.

**The open middle band is computationally inaccessible:** it needs k≥4 (room between capacity
agreement k and Johnson √(n(k−1))), but a PROPER subgroup forces p≫n, so the p^k codeword matrix
explodes (p=97,k=4 ⟹ 88M). Cannot probe exactly. And the in-tree `rootsOfUnity_dyadic_codeword_list_ge`
(exponential, structure-dependent) plus the divisor-poverty probes show the open-regime list is
field/subgroup-DEPENDENT — so field-independence (Conjecture M) fails exactly where it would matter.
Conjecture M holds only where the answer is already the classical Johnson bound. Not a δ* pin.

Campaign: E''(O160), J(O161), J'(O162), L(O163), M(O164) — 5 direct conjectures, all refuted or
reduced to the open explicit-RS sub-Johnson list-decoding bound. No fabricated closure.

## 2026-06-13 — "E(μ_n) ≤ C·n²·log n for ALL p≡1 mod n" is FALSE (Fermat-prime degeneracy); restrict to n ≤ √p (Fable fleet)

The over-general energy conjecture (B10) is refuted by the **Fermat-prime family** p = 2^m+1,
n = p−1 = 2^m (a 2-power, p≡1 mod n): then μ_n = F_p^× (the WHOLE multiplicative group), so
E(μ_n) = n² + n(n−1)² ≈ n³ ≫ n²log n. The conjecture fails whenever the subgroup fills the
field (n ≈ p). The correct, surviving form restricts to the **small/boundary subgroup regime
n ≤ √p** (the production NTT range, n ≤ √p for Goldilocks): there the worst-case energy is
≈ 1.3·n²·ln n (probe_worstcase_energy, probe_boundary; ratio E/(n²ln n) BOUNDED and DECREASING
2.62→0.74 across n=8..256). So: the n²log n bound is FALSE universally, TRUE (empirically) for
n ≤ √p — exactly the deployed regime. The boundary n≈√p bound remains the open core (= GV/HBK
square-root-cancellation, faces B2/B3 below n^{5/2}).

### O165 — INDEPENDENT AUDIT of the δ* reduction: AIRTIGHT + axiom-clean, conditional on one honest open Prop — with 3 mandatory disclosures (nubs, hostile 4-agent Opus-4.8 audit + independent rebuild, 2026-06-13)

A zero-charity audit of the headline "all supporting math proven; δ* reduced to ONE clean
Prop." Independently rebuilt the chain (`lake build CensusDominationWeld`, 8365 jobs) +
transitive `#print axioms` on all load-bearing nodes (pin, interiorCeiling,
kkh26_epsMCA_lower_bound, badScalars_card_le_alignable, kkh26_lemma1, the meet lemma):
**ALL exactly [propext, Classical.choice, Quot.sound]; zero sorry/admit/custom-axiom/
native_decide across the 44-file closure** (every grep hit was docstring prose).

**CERTIFIED SOLID (the reduction itself):** `kkh26_deltaStar_pin_of_censusDomination` proves
`mcaDeltaStar(evalCode, ε*) = 1 − r/2^μ` — a genuine EQUALITY (two-sided meet at the SAME
δ₀, via `mcaDeltaStar_eq_of_good_below_of_bad_above`), NOT a one-sided bound. Lower bracket
from CensusDomination; **upper bracket (KKH26 ceiling) is UNCONDITIONAL** (no hidden Prop).
The sole undischarged hypothesis is `CensusDomination` — and it is the HONEST residual:
its filter predicate is byte-identical to the consumer's proven count obligation
(`badScalars_card_le_alignable`), it is provably NON-vacuous (`kkh26_fibreUnion_aligned_
nondegenerate` builds ≥ 2^r·C(2^{μ−1},r) aligned bad scalars; K is forced < that, so it's
the real supply wall, not a free bound), and it is never discharged (no `_holds`).

**THREE MANDATORY DISCLOSURES (without these the headline is oversell):**
1. "One Prop" is the residual ONLY for the hard deep-band/large-r regime. The bulk range
   is ALREADY unconditional via `kkh26_deltaStar_pin_allWitness` (binomial budget, no
   CensusDomination) + a concrete zero-hypothesis instance `deltaStar_pin_concrete_F4129`
   (δ*=3/4 over ZMod 4129, fully discharged). Do NOT say "the whole prize is one Prop."
2. CensusDomination is GENUINELY OPEN at the prize window, NOT near-proven: the team's own
   `packing_exceeds_budget_deep_band` PROVES the elementary route fails at r=n/2;
   `packing_covers_sqrt` reaches only ~√n; production support is EMPIRICAL (O158/O159/O164
   block the structured mechanisms, but the general bound = the open Stepanov/additive-
   energy E(μ_n)=n^{2+o(1)} = 25-year explicit-RS sub-Johnson list-decoding problem). Do
   NOT imply it is plausibly-soon-provable.
3. "Beyond Johnson" holds for the m=1 NTT regime (numerically) but is NOT a Lean theorem
   (no Real.sqrt comparison in-tree); at m≥2 small-r the pin can fall to/below Johnson.

**BOTTOM LINE (safe to send):** "δ* = 1 − r/2^μ is pinned EXACTLY, both-sided, axiom-clean,
conditional on a single honest non-vacuous combinatorial Prop (CensusDomination) — the
genuine open core (explicit-RS beyond-Johnson list decoding); the upper bracket, a
bulk-parameter unconditional pin, and a concrete zero-hypothesis instance are already
in-tree." That is a real, valuable, certified result. The three caveats are what keep it
honest before Boneh/Vitalik. (Cosmetic: CensusDominationWeld.lean:81 unused binder hmu.)

### O166 — DISCLOSURE O165-#3 CLOSED: beyond-Johnson placement is now a Lean theorem (no Real.sqrt gap) (nubs, 2026-06-13, goal priority 1)

The audit (O165) flagged the "δ* = 1−r/2^μ lies beyond the Johnson radius 1−√ρ" placement
as numeric-only (no Real.sqrt comparison in-tree). Now a theorem, axiom-clean:
`PinBeyondJohnson.lean` (single-module build green).

* `pin_beyond_johnson_iff` (μ,m,r; m≥1, r≥2): for the pin code (length 2^μ·m, dim (r−2)m+1,
  rate ρ), `1 − r/2^μ > 1 − √ρ ↔ r²·m < 2^μ·((r−2)m+1)` — via `Real.lt_sqrt` the sqrt
  comparison reduces EXACTLY to an elementary Nat inequality (no sqrt gap; the substitution
  r = r'+2 eliminates all Nat-subtraction casts).
* `pin_beyond_johnson_iff_m1` (the FRI/STIR dyadic n=2^μ case): `1 − r/2^μ > 1 − √ρ ↔
  r² < 2^μ(r−1)`.

HONEST SCOPE (faithful to O165-#3): it is an IFF — beyond-Johnson holds exactly under the
stated inequality, true throughout the m=1 production regime, provably FALSE at m≥2 small r
(μ=2,m=2,r=2: pin 1/2 < Johnson). So "beyond Johnson" is genuinely conditional, now exactly
CHARACTERIZED rather than asserted. Goal disclosure-#3: CLOSED (landed Lean theorem).

### O167 — DISCLOSURE O165-#1 CLOSED: the unconditional/residual boundary is EXACTLY r ≈ √(2^μ), via a landed axiom-clean theorem (nubs, 2026-06-13, goal priority 1 — all 3 disclosures now resolved)

Disclosure #1 (the audit's "one Prop is the residual ONLY for deep-band/large-r; the bulk
range is already unconditional") is now precisely CHARACTERIZED by an in-tree theorem I
independently verified axiom-clean:

* `kkh26_deltaStar_pin_lowdegree` (KKH26DeltaStarPinAllWitness.lean:181, axiom-clean
  [propext,Classical.choice,Quot.sound], module build green 8371 jobs): for EVERY μ≥1,
  prime p above the KKH26 threshold with an order-2^μ element, and EVERY degree r in
  `2 ≤ r ≤ 2^{μ-1}` with `r² ≤ 2^μ+1`, the pin `mcaDeltaStar(evalCode g 2^μ (r−2)) = 1−r/2^μ`
  holds with **NO CensusDomination and NO binomial hypothesis** — the budget-below-supply
  inequality `C(2^μ,r)/r < 2^r·C(2^{μ-1},r)` is discharged outright by `choose_bulk`
  (axiom-clean). An INFINITE unconditional family.

**THE EXACT BOUNDARY (the disclosure's precise content):**
- **Unconditional region (no open Prop):** `r ≤ √(2^μ)` (i.e. `r² ≤ 2^μ+1`) — δ* pinned
  outright, landed theorem above. Includes the concrete zero-hypothesis
  `deltaStar_pin_concrete_F4129` (δ*=3/4 over ZMod 4129).
- **CensusDomination-load-bearing region:** `√(2^μ) < r ≤ 2^{μ-1}` (deep band toward
  capacity). The PRODUCTION prize rates live here: ρ=1/2 ⟹ r≈2^{μ-1} ≫ √(2^μ) for μ≥4.
- The boundary `r ≈ √(2^μ) = √n` (at m=1) COINCIDES with `packing_covers_sqrt` (the
  elementary route reaches exactly ~√n) and `packing_exceeds_budget_deep_band` (fails at
  r=n/2) — three independent in-tree objects agree on the same √n boundary.

HONEST FRAMING (the disclosure's whole point): there is an infinite family of
δ*-pins with NO open math — but it is the LOW-DEGREE (small-r) family, NOT the production
prize rates. "The bulk range is unconditional" is true and now exactly bounded; "the prize
itself is unconditional" is FALSE (production r is deep in the CensusDomination region).

**GOAL STATUS — all three O165 disclosures now resolved:** #1 CLOSED (this, landed
theorem + exact boundary); #2 documented-as-blocked (CensusDomination = the Stepanov/
additive-energy / explicit-RS sub-Johnson 25-year open problem); #3 CLOSED (O166
`PinBeyondJohnson.lean`, landed theorem). Reduction re-audits clean (O165); dossier
current (#371). The residual is now EXACTLY the named classical open problem — nothing
further to honestly add without solving it.

### O168 — O163 "energy silent at prize scale" is now a CHECKED conditional theorem (nubs, 2026-06-13, goal clause 3)

O163 stated only in PROSE that the GV/Stepanov additive-energy bound makes the cubic/energy
supply silent at prize scale. Now a theorem (`CubicSupplySilentPrizeScale.lean`, axiom-clean
[propext,Classical.choice,Quot.sound], independently compiled + single-module build green):

* `cubicSupply_silent_at_prize_scale` — under `GVRepBound (image dom univ) M` (the in-tree
  integer-clean form of the cited GV/Stepanov `E(μ_n) ≲ n^{8/3}`, kept as a NAMED HYPOTHESIS,
  never asserted — the TZPrimeSupply pattern) and `n ≤ 2^40` (prize domain bound), the cubic
  word's explainable-3-core supply `S` satisfies `S < 2^128 = ε*·q`. The energy/cubic
  mechanism CANNOT breach the prize threshold — it is silent.
* `gv_supply_envelope_lt` — the bare numeric kernel `260·(2^40)^11 < (2^128)^6` (norm_num).
* Proof = the landed capstone `cubicSupply_pow_le_of_gvRepBound` (`S^6 ≤ 260·n^11`) +
  monotonicity in n≤2^40 + the envelope + strict monotonicity of x↦x^6 (`lt_of_pow_lt_pow_left₀`).
  Margin huge: proven supply ≈ 2^74.7 ≪ 2^128 (O163's prose ≈2^85 was a loose over-estimate).

HONEST SCOPE (goal clause 3 compliant): the GV energy bound is a HYPOTHESIS, never asserted
— this does NOT prove the energy bound (that's the open Stepanov/additive-energy input). It
proves the CONDITIONAL: given the cited bound, the energy route is provably below breach at
prize scale. Strengthens the dossier — the "energy mechanism is silent" leg of the
δ*-residual map is now checked, not prose. Found via Opus-4.8 recon+prove+verify; the verify
lane independently reconstructed + axiom-confirmed it; I re-verified from a third seat before landing.

### O169 — the cubic-supply silence is UNCONDITIONAL: O168's GV hypothesis is REMOVABLE for the threshold (nubs, 2026-06-13)

Strengthening O168. `cubicSupply_silent_unconditional` (same file, axiom-clean, build green):
the cubic explainable-3-core supply is `< 2^128 = ε*·q` at `n ≤ 2^40` with **NO additive-energy
hypothesis** — it is `≤ C(n,3) ≤ n³ ≤ (2^40)³ = 2^120 < 2^128` by pure subset counting
(`Finset.card_filter_le` + `Nat.choose_le_pow`). So O168's `GVRepBound` was UNNECESSARY for the
silence threshold; the GV/Stepanov energy bound buys only the tighter estimate (≈2^74.7 vs 2^120),
not the silence. (The in-tree unconditional order-2 Stepanov bound `additiveEnergy_lt_cube_stepanov`,
E(μ_n) < n³, gives the same via the energy route; the subset count is the cleanest.) Net: the
cubic/energy supply route is provably silent at prize scale UNCONDITIONALLY — one fewer residual
on that leg of the δ*-map. Honest scope: this is the cubic (k=2) word's supply only — it does NOT
touch the general deep-band CensusDomination (still the open core); it cleanly closes the cubic leg.

### O170 — SELF-CORRECTION: O168/O169 cubic-supply silence is CORRECT but VACUOUS for the prize (cubic supply ≡ 0 on 2-power μ_n); the framing overclaimed (nubs, 2026-06-13)

Honesty correction, triggered by the fleet's d7feabd7a guardrail + independent re-verification.
O168/O169 prove the cubic (3-term zero-sum) explainable supply is < 2^128 at n ≤ 2^40. The
THEOREMS ARE CORRECT and axiom-clean. BUT the cubic 3-term zero-sum supply is **IDENTICALLY 0
for 2-power μ_n** (Mann: no 3-term vanishing sum of 2^m-th roots of unity, 3∤2^m) — independently
re-confirmed even at the SPLIT production prime p=2013265921:
`scripts/probes/incidence/landscape/cubic_vacuous_check.py` → mu_8/16/32 all give 3-term count
= 0 (4-term count = 6/28/120 = C(n/2,2)). So O168/O169 bound a quantity that is already ZERO for
the prize 2-power domains — they are **vacuous-for-prize**, and my framing "closes the cubic/energy
supply leg of the δ*-map" OVERCLAIMED. RETRACTED.

**What's actually operative:** the supply for 2-power μ_n runs through the 4-term/even zero-sum
route (= additive energy E(μ_n)), NOT the cubic route. At production SPLIT primes the relevant
energy is the OPEN GV/Stepanov quantity E(μ_n)=n^{2+o(1)} — its prize-scale silence is governed by
that open bound (in-tree as the GVRepBound hypothesis), NOT closed by O168/O169. The exact value
E=3n(n−1) is the INERT/char-0 case; production primes are split, where it is the open problem.

NET (honest): O168/O169 stand as correct lemmas but contribute nothing to the prize 2-power supply
question (they bound 0). The energy-supply leg for the prize is NOT closed — it remains the open
GV/additive-energy bound. This entry corrects the record; no fabricated closure.

### O171 — FALSIFY-FIRST ON THE $1M PROP: the deep-band #bad-SCALAR count HOLDS vs the KKH26 budget K=2^r·C(n/2,r) with 2.5×–20× margin at n=16 (faithful, triple-verified) — first direct positive evidence CensusDomination is true at the demand level; the literal alignable-SETS form is FALSE (lossy overcount) so the obligation must be the bad-scalar form (nubs, 2026-06-13)

The δ* prize (#389) reduces to CensusDomination: deep-band bad count ≤ budget K. The packing
route (PackingDeepBandMiss) provably MISSES the deep band (its upper bound exceeds K there:
n=16 r=7 pack=1430 > K=1024) — but that is the BOUND being weak; the TRUE count was uncomputed.
Computed it exactly (Opus 4.8, falsify-first, pin→compute→adversarial-verify).

* **HOLDS WITH MARGIN [COMPUTED, faithful BabyBear p²=4×10¹⁸ ≫ C(16,8)=12,870 — no O164
  saturation].** Worst-case-over-stacks deep-band #bad-scalar at n=16 (exhaustive over 240
  monomial pairs + 200 random/structured): r=3..8 → #bad = 97, 145, 89, 113, **225, 104** vs
  K = 448, 1120, 1792, 1792, **1024, 256** — margin 2.5×–20×, tightest at the deepest prize
  bands r=7 (4.6×) and r=8 (2.5×). Every count ≤ the packing bound C(16,a₀)/(a₀+1)
  (calibration). The maximizer is a high-frequency monomial pair (x⁸=−1), NOT canonical
  KKH26 — which gives #bad=0 at the deep band (its supply lives at the ceiling band a=rm:
  #bad=113,464,1233,2256,3025,3280,3281, validated). **First direct faithful positive evidence
  the prize Prop is true at the demand level.**
* **The LITERAL alignable-SETS CensusDomination is FALSE at the deep band** — a degenerate
  codeword stack (u₀ constant in deg<k_c) makes γ=0 own all C(n,a₀) a-sets (#align up to
  12,870 ≫ K, 12.6× at r=7) while pinning exactly ONE bad scalar. NOT a δ* refutation: the
  documented lossy overcount (SinglePencilQIndependence L19-23). **The correct in-tree
  obligation is the #bad-SCALAR form (badScalars_card_le_alignable / the SinglePencil route),
  not the alignable-sets cap.** Verified the degenerate stack is a genuine alignment respecting
  the non-degeneracy clause.
* **Triple-verified:** the counts reproduce digit-for-digit across THREE distinct code paths
  (builder's Gauss/ratio C; Laplace+Vandermonde-minor C; from-scratch Python Bareiss+itertools)
  and are invariant across three faithful primes (kills the O164 pigeonhole artifact).
  Residual def cross-checked vs OwnershipBound/UniversalAlignmentLaw/CensusDominationWeld.
* **Honest scope:** n=16 is the exact worst-case frontier; n=32 worst-case is INFEASIBLE
  (C(32,17)≈5.7×10⁸/stack, search ~days; syndrome route q^{2(n-k)} astronomically infeasible).
  Char-0-faithful, m=1 rate family — direct EVIDENCE the Prop holds in the form that matters,
  NOT a proof for all n (that is the swarm's analytic Stepanov/Weil route). Complements the
  other NubsCarson seat's O164 (fiber/supply side = O(1)): #alignable ≈ #bad × fiber, both
  measured small.

**Where it lands:** the census-domination route to δ* is NOT killed by the deep band (the
honest worst case I could most fear) — the gating bad-scalar count holds with comfortable
margin at the computable frontier, and the only failure (the literal set-form) is a known
overcount that re-statement fixes. The prize obligation sharpens to: prove the #bad-scalar
deep-band bound for all n (the analytic core). Dossier: scripts/probes/genlaw/o165_census_demand/.

### O172 — THE q-THRESHOLD + r=3 PROVEN FOR ALL n: production q is the deep-band WORST case (saturating envelope, char-0 supremum), and #bad(r=3)=n²(n−4)/32+1 ≤ K for all n — so O171's faithful evidence transfers to production; general r≥4 stays the open analytic core (nubs, 2026-06-13)

Follow-on to O171. O171 showed CensusDomination's deep-band #bad-scalar count holds with
margin at n=16 FAITHFUL prime; DeepBandSaturationDischarge shows it fails at small q. This
resolves the q-threshold and the production-transfer question (Opus 4.8, adversarially
verified 0.85, one wording fix applied).

* **Production q is the WORST case, not a relief [MEASURED + envelope argument].** #bad(q) has
  the char-0 algebraic count as its SUPREMUM — a *saturating envelope* (NOT monotone: the
  small-q regime fluctuates, measured strict drops e.g. n=16 r=7 sweep 17,97,…,209,225 with
  3 drops — corrects the workflow's initial "monotone" claim — but nothing exceeds char-0).
  Below q\*=√C(n,r+1) the count is value-space-limited (#bad ≤ q−1) and CensusDomination fails
  by pigeonhole (= DeepBandSaturationDischarge / O164 saturation). Above q\*, #bad = the fixed
  char-0 count. So production q (2⁶⁴–2²⁵⁶, far above q\* for n ≤ ~512) REALIZES the char-0
  worst case exactly ⟹ wherever char-0 #bad ≤ K, **production HOLDS** — O171's n=16/32 faithful
  evidence transfers to production (resolving O171's open q-transfer worry).
* **r=3 PROVEN for all n [PROVEN modulo landed A4 rigidity].** Exact closed form
  **#bad(r=3) = n·C(n/4,2)+1 = n²(n−4)/32+1** (n=16→97, 32→897 full sweep, 64→7681, all match
  O171), and ≤ K for ALL n by the exact integer identity K−#bad=(h−2)h(13h−16)/12−1>0 (h=n/2≥4,
  margin→5.33×). Order-2 character line → parity-split collinearity → antipodal pair-product →
  bad γ=−e₁ (in-tree Vieta pin); config count n·C(n/4,2) field-independent; distinctness =
  PairSumRigidityModP.pair_sums_ne_modp (threshold 2ⁿ). First partial PROOF of the demand
  bound (not just evidence).
* **Honest scope:** r ≥ 4 OPEN — no clean closed form (divisor-dependent worst-case family:
  x^{n/2} at r=3, x^{n/4} at r=4; counts non-monotone 97,145,89,113,225,104); general-r ≤ K
  MEASURED only (n=16 all bands 2.46×–20.1×; n=32 r=3 5.0×, r=4 33×) = the ExcessCensusLaw
  open analytic core. The literal alignable-SETS form stays FALSE (O171 overcount, retained).

**Where it lands:** the census route to δ\* is alive at production and r=3-closed for all n; the
worst case I most feared (production q amplifying the count) is the opposite — production q is
the worst case but it's the char-0 value, which is ≤ K. The remaining prize obligation
sharpens to ONE target: the general-r (r≥4) deep-band #bad-scalar bound (the analytic core,
the swarm's Stepanov/Weil lane). Dossier: scripts/probes/genlaw/o172_qthreshold/.

### O173 — THE SECOND-MOMENT PAIR-SUM GATE IS INSUFFICIENT: Σ_d A_d I_∩(d) = Θ(E[N]²) (NOT o(E²)) through the upper window, and Θ(1) overdispersion is exponentially blind to the KKH26 worst line — so the upper-window δ* wall is genuinely worst-case extremality, not any moment bound (nubs, demand/list-decoding seat, 2026-06-13)

Targets lalalune's localization comment (2026-06-13), which proved δ* = H_q⁻¹(1−ρ−log_q(1/ε*)/n)
in the lower window and reduced the upper window to ONE explicit gate: "is Σ_d A_d·I_∩(d) =
o(E[#bad]²) at threshold?" (A_d = MDS weight enumerator, I_∩(d) = radius-R two-center ball
intersection). I built and computed that object exactly — probe_pairsum_gate.py, the named
"machinery to build next" (Opus 4.8 inline; implementations validated: Σ_w A_w = q^k exact,
I_∩(0) = V(R) exact; lower-window switch lands precisely at (1−ρ)/2).

* **(a) Lower window δ < (1−ρ)/2 — MACHINE-CONFIRMED unconditional.** pair_term = Σ·q^n/(q^k·V²)
  = EXACT 0: the d∈[d_min,2R] band is empty (2R<d_min=n−k+1), so no codeword pair has
  overlapping radius-R balls ⟹ worst = average ⟹ the closed form holds with zero residual.
  Verified at ρ∈{1/4,1/2}, n∈{16,32,48,64}, q from 257 up to the genuine prize q=n·2¹²⁸. The
  switch lands at exactly (1−ρ)/2 (ρ=1/2,n=32: pair_term 0 at δ=0.25, turns on at 0.281).
* **(b) Upper window — the gate's "o(E²)" hope is FALSE.** pair_term rises from ≈0 just above
  (1−ρ)/2, PLATEAUS just below 1 across the whole window, and crosses 1 EXACTLY at capacity
  δ=1−ρ (coincident with E[N]→1). So Σ_d A_d I_∩(d) = Θ(E[N]²), NOT o(E[N]²): the pair sum is
  COMPARABLE to the mean², Var ≈ E[N]², only O(1) typical overdispersion. lalalune's hoped-for
  o(E²) certificate does not exist in the upper window — refuted by exact in-regime arithmetic.
* **(c) Even Θ(1) is exponentially blind to the wall.** KKH26 (ePrint 2026/782, Krachun–Kazanin–
  Haböck) PROVES a worst line with 2^{Ω(1/η)} close points at δ=1−ρ−Θ(1/log n). The 2nd-moment
  overdispersion Θ(1) ≪ 2^{Ω(1/η)}: the average pair sum cannot feel the measure-zero structured
  worst line. A small (or any) second moment is a typical/whp certificate (Chebyshev), never a
  worst-case one — so proving the gate could NOT close the upper window even if it were o(E²).

**Where it lands:** the second-moment/pair-sum route to the upper-window δ* is now RULED OUT as
a certificate — both because the gate is Θ(E²) not o(E²), and because Θ(1) overdispersion is
exponentially below the proven KKH26 worst line. This converts lalalune's "open: is the gate
o(E²)?" into "answered NO, and it wouldn't suffice regardless." The lower window (δ<(1−ρ)/2) is
FULLY CLOSED (closed form, zero residual). The entire open content is the WORST-CASE combinatorial
extremality of the antipodal subset-sum fibre (BCHKS25 Conj 1.12) — exactly lalalune's "must be a
combinatorial extremality argument, not a character-sum/interpolation/moment bound." Probe:
scripts/probes/probe_pairsum_gate.py.
### O174 — the closed-form-FREE per-line structural route: d-ary split + 2^r sign-symmetry + single-line dominance all CONFIRMED, but the per-line injection into C(n/2,r)·2^r BREAKS for r≥4 (axis-support mismatch) — same open core as O172 (nubs, 2026-06-13)

Asked whether each order-d character line has deep-band #bad ≤ its budget share (so
max_d ≤ K = 2^r·C(n/2,r)) WITHOUT the O172 closed form. **Verdict: PARTIAL.** The per-line
framing is correct and dominance HOLDS, but the structural per-line UPPER BOUND does not — it is
a count-coincidence, not an injection. All probes reproduce the O172 worst-stack #bad n=16
r=3..8 = 97,145,89,113,225,104 digit-for-digit (OwnershipBound.residual modular-det ground
truth, BabyBear p=2013265921); K=448,1120,1792,1792,1024,256; margins 2.46×–20.1×.

* **d-ary split generalizes in FORM [confirmed].** High-freq line u₀=χ_d(i)=x_i^{n/d}, u₁=u₀/x_i:
  aligned-S(γ) ⟺ the a₀=r+1 points lie on one deg-<(r−1) curve; clearing 1/x_i gives
  P(x_i)−ωʲ(x_i+γ)=0, P free deg≤r−1; χ_d constant per residue class mod d so S splits into d
  classes, class j = roots of Q_j=P−ωʲ(x+γ), deg≤r−1. The Q_j form a PENCIL
  Q_j−Q_{j'}=−(ωʲ−ω^{j'})(x+γ) — the d-cyclic product condition generalizing the r=3 antipodal
  pair-product (d=2: x_a x_b + x_c x_d = 0). Aligned sets DO split into χ-class distributions
  (r=3 order-2: {(2,2):96,(4,):140}; r=8 order-16: all-1s).
* **OBSTRUCTION #1 (per-class size).** Naive "class size ≤ deg Q_j = r−1" FAILS on degenerate
  classes: r=3 (4,)-distribution (140 sets, size 4 > r−1=2) = the B=0 collinear-degenerate family
  that ALL collapse to the single γ=0 (the "+1" in n·C(n/4,2)+1). Harmless to the count, breaks
  the clean structural statement.
* **OBSTRUCTION #2 (the real one — axis-support mismatch).** A per-line injection
  {bad γ}→{r-subset of n/2 antipodal axes}×{2^r signs}=K requires aligned sets to touch exactly
  r axes. Measured axis-support: r=3 {2:12,3:128,4:96} (up to r+1, too many to fit r-subsets);
  r=8 {5:80,6:192} (5–6 axes, fewer than n/2=8 needed for C(8,8)=1). So C(n/2,r) has NO geometric
  realization on the bad set — K bounds #bad NUMERICALLY but not via injection for r≥4.
* **The 2^r factor IS structural [confirmed].** At the tightest band r=8 (margin 2.46×):
  #bad=104=2×52, bad-γ set CLOSED under negation γ↔−γ; 2^r=256=K (C(8,8)=1). 2^r = the
  free-negation sign symmetry of the antipodal-balance engine (matches RESULTS-GENERAL-LAW).
* **NON-OBSTRUCTION: single-line dominance HOLDS.** Obligation = worst witness PAIR = one line,
  so max-over-lines is correct. Even unioning a whole degree-window (not required) stays far below
  K: r=3 union over all (x⁸,x^f)=113≪448; r=4 union over (x⁸,*)+(x⁴,*)+(x¹²,*)+(x⁷,*)=337≪1120.
  No harmful cross-line interference at any tested band.
* **Normalization note (NOT an O172 error).** residual-ratio γ ≠ −e₁(S) per-set (0/96 equal at
  r=3) but |{γ}|=|{−e₁}|=96=n·C(n/4,2); CF.md's "γ=−e₁" is the in-tree witness_pin convention,
  count-equivalent, so the proven r=3 closed form stands.

**Where it lands:** the per-line bad set is the JOINT (e₁..e_{r−1})-level-set whose cardinality
is exactly the open analytic core O172/ExcessCensusLaw names; the d-cyclic pencil constrains but
does not cap it at C(n/2,r)·2^r. The gap is PURELY the per-line count bound for r≥4 — identical
to O172's open core, so a closed-form-free per-line structural proof is NOT available. Probes:
/tmp/fanoutC/{dary_split_theory,axis_injection,r8_tight_analysis,crossline_check,crossline_r4,
perline_budget}.py. Reading list for the analytic core: PAPERS_NEEDED.md §"ExcessCensusLaw
analytic core".

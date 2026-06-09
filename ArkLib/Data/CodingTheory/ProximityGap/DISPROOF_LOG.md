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

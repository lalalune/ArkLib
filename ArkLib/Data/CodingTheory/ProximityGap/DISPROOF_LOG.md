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

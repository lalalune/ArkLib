# Disproof Log — ABF26 Proximity Prize Grand Challenge 1 (Issue #232)

Goal: keep trying to **disprove** the ABF26 Grand-Challenge-1 conjecture, then
**disprove the disproof**. Record every attempt so we don't repeat ourselves and
so we zero in. Keep lemmas that *constrain* even if they don't fully disprove.
Default assumption: my disproof is wrong — find the precise reason it fails and
make that reason a sorry-free Lean lemma.

## The target

`MCAGS.epsMCAgs_prizeBound_conjecture` (and `uniformEpsMCAgsPrizeBoundConjecture`):
there exist universal `c₁,c₂,c₃` such that for every prize rate `ρ = prizeRates j`,
gap `η > 0`, and radius

    δ ≤ 1 − ρ − η          (★ strictly below list-decoding capacity 1−ρ)

the GS-exposed MCA error obeys

    epsMCAgs(RS_ρ, δ, L) ≤ (1/q) · (2^m)^{c₁} / (ρ^{c₂} η^{c₃}).

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

## Open angles not yet tried (to avoid repetition)

- O4: try to *realize* the O3 obstruction — construct a Frobenius-stable `(u₀,u₁)` with a
  high-degree bad scalar at radius in the live band `[1−√ρ, 1−ρ−η]` (the only place it could exist).
  If the proximity-gap "small-or-everything" dichotomy provably forbids a lone orbit in the gap that
  *constrains further*; if it permits one, that is the disproof.
- O5: examine whether `epsMCAgs`'s GS-row restriction (strictly rarer than the raw line-close event,
  via `epsMCAgs ≤ epsCA`) caps the bad count below the Frobenius lower bound, refuting O3-style
  growth outright.

# Disproof Log — ABF26 Proximity Prize Grand Challenge 1 (Issue #232)

Goal: keep trying to **disprove** the ABF26 Grand-Challenge-1 conjecture, then
**disprove the disproof**. Record every attempt so we don't repeat ourselves and
so we zero in. Keep lemmas that *constrain* even if they don't fully disprove.
Default assumption: my disproof is wrong — find the precise reason it fails and
make that reason a sorry-free Lean lemma.

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

## Open angles not yet tried (to avoid repetition)

- O8: strengthen O7 to **fixed-gap** Frobenius realization: produce high-degree bad scalars with
  some constant `η > 0` independent of extension degree, or prove this is impossible. *(Partially
  probed by O7′: fixed-gap prime-field samples show NO list growth — leans toward "impossible";
  needs exhaustive worst-case search or a proof, and the `GF(2^s)` Frobenius version.)*
- O9: repair/formalize the GS RHS domain-size linkage: add or consume a hypothesis
  `Fintype.card ι = 2^m` (or a comparable smooth-domain size condition) before using
  `epsMCAgsPrizeUniversalConjecture` as the prize-facing statement.
- O10: attack via a *list-size lower bound* in the band `(1−√ρ, 1−ρ−η]` at fixed `η` — the O6′
  reduction shows this is the only remaining disproof route; connect to known RS capacity
  list-decoding lower bounds (Ben-Sasson–Kopparty–Radhakrishnan / Guruswami–Rudra) and check whether
  any apply at a prize rate with fixed positive gap.

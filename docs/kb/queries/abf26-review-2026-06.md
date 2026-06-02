# ABF26 PR #505 — Adversarial Review + Refined Roadmap (2026-06-02)

Branch `feat/abf26-plan`. Reviews the formalization of *Open Problems in
List Decoding and Correlated Agreement* (Arnon, Boneh, Fenzi; April 8, 2026)
against three goals the user set:

1. **Full coverage** of the paper.
2. **Idiomatic integration** with ArkLib — reuse existing definitions, place
   material in the right files, *no duplicate definitions, no paper-shape
   alias wrappers*.
3. The **grand challenge is a prize** instantiable over a *range of
   parameters* (rate `ρ ∈ {1/2,1/4,1/8,1/16}`, `ε* = 2^-128`); the statement
   must let us *instantiate the theorem across that whole range and make
   incremental progress per rate.*

Companion artefacts: the per-item audit
[`audits/open-problems-...md`](../audits/open-problems-list-decoding-and-correlated-agreement.md),
the prior roadmap [`abf26-pr-roadmap.md`](abf26-pr-roadmap.md), and the
2026-05 review log [`abf26-review-2026-05.md`](abf26-review-2026-05.md).

All findings below were verified against the working tree (Lean build,
`grep`, file reads), not against the docs.

---

## 0. Verified ground truth (2026-06-02)

- **Lean build is GREEN** (`lake build`, 4101 jobs, 0 errors). Only `sorry`
  and pre-existing style warnings.
- `./scripts/validate.sh` **exits 1**, *solely* from **11 broken markdown
  links** in `docs/kb/ABF26_PLAN.md` (1) and `docs/kb/ABF26_POLISH_PLAN.md`
  (10) — stale paths like `ABF26Prelims.lean`, `JohnsonBound/ABF26.lean`,
  `ListDecodingBounds.lean`, `Connections.lean`. **No Lean regression**, but
  the repo gate is red.
- **40 real proof-`sorry`s** across the 21 ABF26-owned files, **every one a
  tagged external-admit with a citation**. `coverage.py` and `lint.py` pass.
- Audit's six "sorry-free" claims (`epsMCA`/`epsCA`, `dim_irsCode`,
  `extensionCode_smul_mem`, grand-challenge predicates, B.1,
  `accepts_of_inputRelation`) all **verified true**.
- Coverage by audit status: 38 present(-proven), 10 present-but-different,
  9 present-but-incomplete, 3 deferred, **0 missing**. 87 paper items tracked.

The statement layer is in genuinely good shape, faithfully shaped, and the
reuse discipline is unusually strong. The issues below are about **what the
40 sorries hide**, the **prize-instantiation gap**, and **hygiene**.

---

## Part I — Issues that must be fixed

### A. Honest-scope framing: the paper's *own* contributions are largely unproven

This is the central adversarial finding. ABF26 is a **survey**: ~40 of its
theorems are results imported from *other* papers (BCIKS20, GG25, CZ25,
BCHKS25, AHIV17, GCXK25, …) and stated **without proof**. Formalizing each in
full is a multi-paper effort and is *legitimately* left as a cited `sorry`.
That part of the work is done well.

But the paper does have **self-contained content it proves in full**, and
*that* is what "formalizing the paper" must actually deliver:

| Paper's own result | Proof in paper | Lean status |
|---|---|---|
| F4.5 `ε_pg ≤ ε_ca ≤ ε_mca` | §4.1 | ✅ proven |
| R4.2 `ε_ca` discretization | §4.1 | ✅ proven |
| L4.7 interleaving degrades MCA `≤ t·` | §4.1 | ✅ proven |
| B.1 collision bound | App. B | ✅ proven |
| **C6.2 completeness** | §6.1 (honest case) | ❌ `sorry` (framework-blocked) |
| **L6.6 knowledge soundness** | §6.2 full proof | ❌ `sorry` |
| **L6.8 round-by-round KS** | §6.2 full proof | ❌ `sorry` |
| **L6.10 simplified-IOR soundness** | §6.4 (adapt L6.8) | ❌ `sorry` |
| **L6.12 list-decoding LB attack** | §6.4.1 full proof | ❌ `sorry` |
| **L6.13 CA LB attack** | §6.4.2 full proof | ❌ `sorry` |
| **§6.3 Tables 2–5** (concrete params) | §6.3 derivation | ❌ **absent** |

**The entire §6 toy problem — the paper's headline original contribution and
the whole reason MCA + list-decoding bounds matter for SNARKs — is stated but
not proven.** L6.12 and L6.13 *have full elementary proofs in the paper* (and
B.1, their key lemma, is already closed in-tree), so they are *in-tree
provable now*, not external admits. Labelling them "external admit" in the
code is a category error — they are the paper's own results.

**Action:** Re-tag the §6 sorries to distinguish "paper proves this; we owe a
Lean proof" from "imported from cited paper; admit is acceptable". Then prove
the former (see Roadmap Phase 2). The PR description must not claim "the paper
is formalized" while §6 is unproven; it currently formalizes *statements*.

### B. Grand-challenge prize instantiation — the user's headline ask is unmet

`ProximityGap.grandMCAChallenge (C : LinearCode ι F) (ε_star : ℝ≥0)` and
`grandListDecodingChallenge` (`GrandChallenges.lean:68,85`) are correctly
shaped, non-vacuous maximality predicates (`∃ δ*≤1, bound(δ*) ∧ ∀ δ>δ*,
¬bound(δ)`). **But they are purely abstract**, and verification confirmed
**zero connecting tissue** to the prize regime:

1. **No Reed–Solomon instantiation.** `grandMCAChallenge`/
   `grandListDecodingChallenge` are referenced *only* at their definition
   site. There is no `grandMCAChallenge (ReedSolomon.code …) ε*` target.
2. **No rate-regime scaffolding.** Nothing pins `ρ ∈ {1/2,1/4,1/8,1/16}`. No
   enumeration, no per-rate target skeleton. The rate set lives only in
   docstring prose.
3. **`ε* = 2^-128` is encoded nowhere** (free `ℝ≥0` by design).
4. **No bridge to `CapacityBounds.lean`.** The RS upper/lower `ε_mca`/`ε_ca`
   bounds that would *resolve* the challenge (`rs_epsMCA_johnson_range_bchks25`,
   `frs_epsMCA_capacity_gg25`, `rs_epsCA_lower_capacity_bchks25_kk25`, …)
   exist in a sibling file, but the two files do not even import each other.
   There is no lemma "bound ⇒ challenge witness".

So the predicate cannot today be *instantiated for RS at a given rate*, and
there is no way to *record incremental progress per rate* — exactly the
property the user required.

**Action (Roadmap Phase 1):** build the instantiation framework — an
RS+rate-parameterized challenge target, a witness-carrying `Resolution`
structure, one-sided progress witnesses, and bridges from `CapacityBounds`.
Design below.

### C. §6.3 concrete parametrizations (Tables 2–5) are entirely absent

The prize is fundamentally *quantitative*: §6.3 derives the soundness error
and argument size of Construction 6.2 as functions of `(s, η, t, r)` at
`ρ = 1/2`, for both IRS (Tables 2–3) and FRS (Tables 4–5), over the Koala
Bear prime sextic extension. **None of this is formalized.** `Impl/IRS.lean`
explicitly defers it and ships only the three RS-instantiated reductions; no
FRS instantiation file exists at all. This is the most direct machine-checked
evidence one could give that the toy protocol achieves its claimed security,
and it is missing.

### D. Integration / duplication findings

Reuse discipline is otherwise a model of the no-duplication rule (numeric
`ε_*` built on the existing predicate API with explicit bridges; WHIR MCA
bridged one-way and documented; `ExtensionFieldPresentation` a thin wrapper
over Mathlib `Algebra`/`Basis`; no paper-shape `alias` wrappers found). The
real issues:

1. **`qEntropy` duplicates Mathlib `Real.qaryEntropy`** (`Basic/Entropy.lean:45`).
   ABF26's is the base-`q` normalization (`= Real.qaryEntropy q x / Real.log q`),
   reimplemented from scratch — it never imports or relates to Mathlib's
   version and so forfeits Mathlib's monotonicity/concavity/continuity API
   that downstream items (C3.8, T3.11, T4.17) will need. **Action:** redefine
   as `Real.qaryEntropy q x / Real.log q` *or* add a
   `qEntropy_eq_qaryEntropy_div_log` bridge lemma.
2. **Survey-silo files with no machine-checked content**: `GrandChallenges.lean`
   (0 theorems), `CapacityBounds.lean` (12 sorries / 0 proofs),
   `ListDecoding/Bounds.lean` (11/0), `Connections/ListDecodingAndCA.lean`
   (4/0), `LineDecoding.lean`. They reuse the right abstractions, so this is a
   *soft* issue, but two of them spawn **fresh single-file directories**
   (`Connections/`, `ListDecoding/`) that are mild parallel-hierarchy smells
   next to the existing `ListDecodability.lean`. **Action:** either
   consolidate placement or state explicitly in the PR that these are
   intentional "paper-table" scaffolds.

### E. Faithfulness defects in §6 statements

Verified against the paper text:

1. **L6.6 / L6.8 drop the paper's `δ < δ_min(C)` hypothesis.** Both only carry
   `0 < δ` (`General.lean` ~496, ~535). The paper requires `δ ∈ (0, δ_min(C))`
   and the proof *uses* `δ < δ_min` (it forces `g = f₁+γ·f₂` from agreement on
   `≥ (1-δ)n > (1-δ_min)n` points). The docstring claims the hypothesis but
   the statement omits it. **Action:** add `δ < Code.minDist`/`δ_min` so the
   eventual proof is sound and the statement matches.
2. **L6.5 drops the `O((s·n)³)` correction-time bound** — states only
   `∃ ecor, SupportsErasureCorrection C ecor`. Acceptable as a weakening, but
   should be flagged in the audit Notes (currently reads as a faithful port).

### F. Hygiene / blockers

1. **`validate.sh` is red** (Issue 0) — 11 broken doc links. Must be green
   before "ready for review".
2. **C6.2 completeness + the broader VCVio gap.** The completeness `sorry`
   (`General.lean` ~453) is blocked on two *general* missing lemmas —
   `simulateQ_forIn` (collapse a simulated guarded `forIn` over
   `List.finRange t`) and a `simulateQ`/`OptionT`/`SubSpec` query-resolution
   simp set. These belong **upstream in VCVio** (`~/VCV-io/`), not ArkLib, and
   would also unblock FRI/Sumcheck completeness. Highest-leverage framework
   investment; see [[pr449-hold-for-lean430]].
3. **C6.9 has no `OracleReduction` flavour** — `OracleVerifier.embed` cannot
   express the `γ`-dependent *combined* output oracle `f₁+γ·f₂` (only verbatim
   subsets of input oracles + messages). A `simOStmt`-based framework refactor
   (sketched in `OracleReduction/Basic.lean:278,293`) is the prerequisite.
   Honestly documented in-tree; tracked here so it is not forgotten.

---

## Part II — Refined roadmap to completion

### Honest "done" levels

- **A — Survey statement layer** (≈current). Every item faithfully stated;
  external imports tagged-`sorry`; audit is canonical map. *Add:* validate
  green, faithfulness fixes (E), qEntropy bridge (D1).
- **B — Paper's own contributions proven.** §6 proofs (L6.6/8/10/12/13 +
  C6.2 completeness), grand-challenge instantiation framework + bridges,
  §6.3 concrete tables. *This is what "the paper is formalized" requires.*
- **C — Downstream-usable.** §6 soundness consumable by real protocols;
  numeric IRS/FRS error bounds wired through. Resolve a first prize rate.

### Phase 0 — Hygiene (hours) — *gate to ready-for-review*

- Fix the 11 broken links in `ABF26_PLAN.md` / `ABF26_POLISH_PLAN.md`;
  `validate.sh` green.
- Re-tag §6 `sorry`s: `paper-proof-owed` (L6.6/8/10/12/13, completeness) vs
  `external-admit` (everything imported). Update audit + PR description so it
  does not over-claim.
- Add the L6.6/L6.8 `δ < δ_min` hypothesis (E1); flag L6.5 weakening (E2).

### Phase 1 — Grand-challenge prize-instantiation framework (the headline)

Goal: make the challenge instantiable for RS at each rate and let progress
accumulate per rate. Concretely, in `GrandChallenges.lean` (or a new
`GrandChallenges/` with `Basic` + `ReedSolomon` + `Resolution`):

1. **RS+rate target.** `def grandMCAChallengeRS (F) [Field/Fintype]
   (domain : ι ↪ F) [Smooth] (k : ℕ) (ε* : ℝ≥0) : Prop :=
   grandMCAChallenge (ReedSolomon.code domain k) ε*`, with a companion that
   takes the rate `ρ` and a proof `k = ρ·|ι|` so call sites read in paper
   terms. Likewise for the list-decoding challenge.
2. **Rate enumeration.** `def prizeRates : Finset ℝ≥0 := {1/2,1/4,1/8,1/16}`
   (or index `j ∈ Fin 4`, `ρ = 2^-(j+1)`), so the prize is a *family* of
   targets `∀ ρ ∈ prizeRates, …` resolvable one ρ at a time.
3. **Witness-carrying resolution.** `structure GrandMCAResolution (C) (ε*)
   := (δStar : ℝ≥0) (le : δStar ≤ 1) (bound : ε_mca C δStar ≤ ε*)
   (maximal : ∀ δ, δStar < δ → δ ≤ 1 → ε_mca C δ > ε*)`. Resolving the prize
   for given params = constructing this. Plus one-sided progress carriers
   `MCALowerWitness` (a `δ` with `ε_mca ≤ ε*`, ⇒ `δStar ≥ δ`) and
   `MCAUpperWitness` (`ε_mca > ε*`, ⇒ `δStar ≤ δ`), so partial progress is
   first-class and the search interval can be tightened incrementally.
4. **Bridges from `CapacityBounds`.** Lemmas turning each RS `ε_mca` upper
   bound (`frs_epsMCA_capacity_gg25`, `rs_epsMCA_johnson_range_bchks25`, …)
   into an `MCALowerWitness`, and each lower bound
   (`rs_epsCA_lower_capacity_bchks25_kk25`, `rs_epsCA_breakdown_cs25`,
   `rs_epsCA_johnson_jump_bchks25`) into an `MCAUpperWitness`. Import the two
   files together. This is the missing connective tissue (B4).
5. **First instantiation.** Instantiate the framework at `ρ = 1/2`,
   `ε* = 2^-128` and record the best current interval `[δStar lower, upper]`
   from the bridged bounds — a concrete, checkable "state of the prize".

Deliverable: someone can write `grandMCAChallengeRS … (ρ=1/2) (2^-128)` and a
partial-progress lemma, then repeat for `1/4, 1/8, 1/16` independently.

### Phase 2 — Prove the paper's §6 contributions

Order by dependency / leverage:

1. **VCVio framework lemmas** (upstream `~/VCV-io/`): `simulateQ_forIn` +
   the `simulateQ`/`OptionT`/`SubSpec` query-resolution simp set. Unblocks
   C6.2 completeness *and* FRI/Sumcheck. Highest leverage. (Fold in with the
   Lean 4.30 / VCVio bump per [[pr449-hold-for-lean430]].)
2. **C6.2 completeness** — close once (1) lands; math core
   (`accepts_of_inputRelation`) already proven.
3. **L6.12 + L6.13** — *in-tree provable now*; B.1 already closed. Follow the
   §6.4 proofs (winning-set lower bounds via the collision/injectivity
   argument). No external dependency.
4. **L6.6 / L6.8 / L6.10** — the substantive knowledge-soundness proofs.
   Depend on the MCA event analysis (`epsMCA`) + the list-size union bound +
   erasure extractor. L6.8 (round-by-round, via `KnowledgeStateFunction`) is
   the canonical one; L6.6 and L6.10 follow. These need real extractor
   construction — largest single effort; may need its own PR each.

### Phase 3 — §6.3 concrete parametrization tables (C-level)

- Formalize the soundness-error and argument-size expressions as functions of
  `(s, η, t, r)` (Tables 2–5), `ρ = 1/2`, Koala Bear sextic extension.
- An FRS instantiation file paralleling `Impl/IRS.lean`.
- Tie to Phase 2's L6.6/L6.8 so the numbers are *derived*, not asserted.

### Phase 4 — Integration cleanups

- `qEntropy` → Mathlib `Real.qaryEntropy` bridge (D1).
- Consolidate `Connections/` and `ListDecoding/` single-file dirs, or justify.
- Resolve the WHIR `hasMutualCorrAgreement` re-expression as a specialization
  of `epsMCA` (D4.3 follow-up noted in audit).

### Phase 5 — Deferred items + remaining in-tree provables

- 3 deferred rows (T3.6, T4.15, R6.14) need a `Data/Probability/UniformSubset`
  primitive (`Pr_{L ←$ (F choose n)}`); build it, then the bounds are cited
  admits.
- T4.8 ε-wrap of AHIV22; T3.2 `johnson_bound_lambda_le_ell` fresh
  Guruswami–Sudan proof; T2.18 UM half (needs the extension-code distance
  result); L2.21 (BCFW25 D.3).
- Close `BCIKS20/AffineLines/Main.lean:40` non-unique-decoding `sorry` via the
  already-added `JointAgreement.lean` machinery (improves a `present-but-
  incomplete` paper dependency).

### Sequencing summary

```
Phase 0 (hygiene) ──► ready-for-review gate
Phase 1 (grand-challenge framework) ──► prize instantiable per rate  [headline]
Phase 2 (§6 proofs)  ── needs VCVio lemmas first (2.1) ──► paper actually proven
Phase 3 (§6.3 tables) ── needs Phase 2 ──► quantitative evidence
Phase 4/5 (cleanup + deferred) ── parallelizable
```

---

## Phase 0 progress log (2026-06-02)

Phase 0 landed (build green throughout, verified by `lake build`):

- **Hygiene:** fixed all 11 broken markdown links — `ABF26_PLAN.md` (the
  `Δ_T(f,g)` notation was being parsed as a link) and `ABF26_POLISH_PLAN.md`
  (root-relative → `../../` paths; split files `ABF26Prelims`/
  `ABF26CodeFamilies` made plain-text; renamed targets `JohnsonBound/Family`,
  `ListDecoding/Bounds`, `ProximityGap/LineDecoding`,
  `Connections/ListDecodingAndCA`). `check-docs-integrity.py` now passes.
- **Re-tagged §6 sorries** `external-admit` → `paper-proof-owed` for L6.6,
  L6.8, L6.10, L6.12, L6.13, and C6.2 completeness (the paper's OWN results);
  L6.5 stays `external admit [GRS25]`. L6.12/L6.13 marked **in-tree provable
  now**. `SoundnessBounds.lean` header rewritten to spell out the two kinds.
- **Faithfulness fix E1:** added the paper's load-bearing `δ < δ_min(C)`
  hypothesis (`δ < (minRelHammingDistCode C : ℝ≥0)`) + `[Nonempty ι]` to L6.6,
  L6.8, L6.10. Build re-verified green.
- **Faithfulness fix E2:** L6.5's dropped `O((s·n)³)` time bound now flagged
  in the audit Notes (was reading as a faithful port).
- Audit rows for L6.5/L6.6/L6.8/L6.10/L6.12/L6.13 updated; `coverage.py` +
  `lint.py` clean.

Remaining Phase 0: none. Next is Phase 1 (grand-challenge instantiation).

## One-line verdict

The PR is an excellent, faithfully-shaped, well-integrated **statement layer**
with strong reuse discipline — but it formalizes the paper's *claims*, not its
*proofs*: §6 (the original contribution) is entirely unproven, the prize
grand-challenge has no RS/rate instantiation or progress scaffolding, and §6.3
is absent. Fix hygiene (Phase 0), build the grand-challenge instantiation
framework (Phase 1), then prove §6 (Phase 2, gated on VCVio lemmas).

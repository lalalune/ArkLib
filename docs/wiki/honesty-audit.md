# Honesty Audit: finding what is not actually proven

This page is the playbook for auditing ArkLib for *unproven-but-presented-as-proven* content —
the "LARP" surface. It complements the automated gates (`scripts/forbidden_tokens.py`,
`scripts/sorry_census.py`, `scripts/axiom_audit.py`) by naming the laundering patterns those
gates do **not** catch, and how to detect them.

## The authoritative live counts (don't trust raw grep)

Raw `grep -r sorry ArkLib/` massively overcounts: most hits are docstring/comment prose
("no `sorry`", de-larp narration). Use the census, which strips comments:

```sh
python3 scripts/sorry_census.py            # JSON: holes vs doc_mentions
python3 scripts/sorry_census.py --fail-on-holes   # CI gate: exit non-zero on any live hole
python3 scripts/axiom_audit.py             # flagship decls must be {propext, Classical.choice, Quot.sound}
```

`holes` = real `sorry`/`admit` in live code. `doc_mentions` = prose. As of the last audit the
ratio was ~40 live holes against ~470 doc mentions — i.e. raw grep overstates by ~12x.

Custom `axiom` declarations are rejected by `forbidden_tokens.py` unless listed in
`scripts/residual_axioms.txt` (each entry is a tracked debt owed to a GitHub issue). That file is
the canonical list of *deliberately retained* unproven external results — currently the
GKL24/BGKS20/BCHKS25/CS25/GG25 capacity bounds (#81–#87) and one KoalaBear residual (#106).

## Laundering patterns the gates miss

The automated gates flag `sorry`, `admit`, `native_decide`, non-allowlisted `axiom`, and
`theorem … : True`. They do **not** flag the following. Audit for these by hand / by build.

1. **Sorry-free wrapper over a sorry dependency.** A `theorem foo_discharged : Real := by exact
   bar h₁ h₂` has no `sorry` in its own body, but `h₁`/`h₂` (or `bar`) transitively contain one.
   It *looks* discharged. **Detection:** `#print axioms foo_discharged` — if it reports
   `sorryAx`, it is not proven. The flagship axiom sweep (`scripts/flagship_axioms.txt`) pins the
   declarations that must stay `sorryAx`-free; anything claiming to "discharge/resolve/close" an
   obligation but not pinned there is suspect.

2. **A `sorry` standing in for a *false* statement.** A hole is worse than open when the stated
   goal cannot hold. Classic tell: a trivial/degenerate construction (e.g. a verifier that accepts
   everything, an all-zeros transcript) under a soundness/extraction claim. Such a `sorry` can
   never be honestly closed; the construction must change. **Detection:** read the construction the
   theorem is *about*, not just the theorem statement.

3. **Non-compiling scaffolding in the manifest.** A file imported by `ArkLib.lean` whose
   declarations don't actually type-check (e.g. an `∃ τ, mcaPrizeLatticeResolved L τ` where the
   predicate needs `domain : ι ↪ F` but is fed a `Finset F`). It contributes "theorems" that never
   compiled. **Detection:** `lake build <module>`; treat a red module as unproven regardless of how
   confident its docstrings sound.

4. **Open-problem-as-theorem.** A `theorem candidate_… : <resolves an open prize> := by sorry`
   dressing a known open problem (the MCA Grand Challenge, WHIR RBR soundness) as a near-complete
   proof. The honest forms are: a named `def …_conjecture : Prop := <statement>` (no proof
   obligation), or a clearly-labeled tracked `sorry`/residual axiom — never a `theorem … := sorry`
   whose name implies it's done.

5. **Re-larp: the same open-problem-as-theorem regenerated.** De-larping one file does not stop a
   new file with the identical shape from appearing. The recurring ArkLib instance is a
   `theorem …_mca_exact_match : ∃ τ, ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved L τ`
   where `L : Finset F` — but `mcaPrizeLatticeResolved` requires `domain : ι ↪ F`, so the
   *statement* is a type error that `sorry` cannot hide, and the file does not compile. Because
   nothing imports these `Candidate*` files, a per-file `lake build` of an unrelated module never
   surfaces the breakage — only a full-manifest `lake build ArkLib` (or `#check @thename`) does.
   **Detection:** `grep -rn "mcaPrizeLatticeResolved [A-Za-z]* " ArkLib --include=*.lean` and check
   each argument is an `ι ↪ F` embedding, not a `Finset`/`Set`; and run a full-manifest build in CI,
   not just changed-file builds.

## Gap in the current gates

`forbidden_tokens.py` + `sorry_census.py` are necessary but not sufficient. They do **not** catch
patterns 1, 2, 3, or 5 above. Recommended additions: (a) a CI step that runs
`lake build ArkLib` (the whole manifest) so non-compiling files imported by `ArkLib.lean` fail the
build even when nothing else imports them; (b) the flagship axiom sweep
(`scripts/axiom_audit.py` against `scripts/flagship_axioms.txt`) extended to every theorem whose
name contains `discharged|resolved|closed|complete|exact_match|keystone` — each must be
`sorryAx`-free or it is laundering.

## Confirmed findings (snapshot — these move; re-run the audit to refresh)

Findings are dated because the live count of holes/larp changes continuously when multiple agents
edit the tree. Treat this section as a worked example of the patterns above, not a current
liability list.

- **WHIR (`ArkLib/ProofSystem/Whir/Protocol.lean`), open obligation #113.** The `whirVectorIOP`
  is built from `whirVerify := fun _ _ => pure true` (accepts everything) and an all-zeros
  `whirMakeTranscript`. `whirVectorIOP_rbrKnowledgeSoundness` was `sorry` and is **false as stated**
  for that stub (an accept-all verifier admits no knowledge extractor — pattern 2), while
  `whir_rbr_soundness_discharged` was a sorry-free wrapper resting on that sorry via
  `whirVectorIOP_isSecureWithGap` (pattern 1). A real verifier (algebraic sumcheck/folding/OOD/
  shift/final checks) plus a genuine RBR-soundness proof — *and a real, statement-dependent honest
  prover, since the all-zeros transcript can never pass real checks* — is the actual #113
  obligation, research scale, per the construction's own comments in
  `ArkLib/ToMathlib/WhirBricksConstruction.lean` (`paperTranscriptVectorIOP`: "perfect completeness
  and RBR soundness still require instantiating `verify` with the algebraic WHIR checks").

- **`ABF26PromotedCandidate.lean` axiom-larp — removed (good).** Previously declared
  `axiom resolves_grand_mca_prize` and `axiom promoted_interleaved_mca_conjecture` — custom axioms
  literally asserting the open MCA prize is resolved (neither was on the
  `scripts/residual_axioms.txt` allowlist). Both have been deleted; the real-axiom count dropped
  from 12 to 10 and `forbidden_tokens.py` is green.

- **`CandidateFrobeniusFold.lean` — re-larp (pattern 5).** A later-added `Candidate*` file in the
  manifest (`ArkLib.lean`) with `theorem frobenius_mca_exact_match : ∃ τ, mcaPrizeLatticeResolved L
  τ` fed `L : Finset F` (needs `ι ↪ F`): a statement-level type error, so the file does not compile
  and breaks a full-manifest build, while its proof comment itself admits the approach is "FLAWED".
  Example of why a full `lake build ArkLib` gate (above) is needed.

## Method to re-run this audit

1. `python3 scripts/sorry_census.py` → live holes, grouped by file.
2. `grep -rn "discharged\|resolved\|_holds\|closed\|complete\b" ArkLib --include=*.lean` on
   theorem/lemma heads → candidate wrappers; `#print axioms` each (needs a build).
3. `lake build ArkLib` (or per-module) → catch non-compiling manifest entries (pattern 3).
4. Cross-check `scripts/flagship_axioms.txt` and `scripts/residual_axioms.txt` against the tree:
   every "flagship" must be `sorryAx`-free; every residual `axiom` must be allowlisted and owe an
   open issue.

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

## Confirmed findings

- **WHIR (`ArkLib/ProofSystem/Whir/Protocol.lean`), open obligation #113.** The `whirVectorIOP`
  is built from `whirVerify := fun _ _ => pure true` (accepts everything) and an all-zeros
  `whirMakeTranscript`. `whirVectorIOP_rbrKnowledgeSoundness` is `sorry` and is **false as stated**
  (an accept-all verifier admits no knowledge extractor — pattern 2). `whir_rbr_soundness_discharged`
  is a sorry-free wrapper that transitively rests on that sorry via `whirVectorIOP_isSecureWithGap`
  (pattern 1); its name overstates the state. A real verifier (the algebraic sumcheck/folding/OOD/
  shift/final checks) plus a genuine RBR-soundness proof is the actual #113 obligation — research
  scale, per the construction's own comments in `ArkLib/ToMathlib/WhirBricksConstruction.lean`
  (`paperTranscriptVectorIOP`: "perfect completeness and RBR soundness still require instantiating
  `verify` with the algebraic WHIR checks").

## Method to re-run this audit

1. `python3 scripts/sorry_census.py` → live holes, grouped by file.
2. `grep -rn "discharged\|resolved\|_holds\|closed\|complete\b" ArkLib --include=*.lean` on
   theorem/lemma heads → candidate wrappers; `#print axioms` each (needs a build).
3. `lake build ArkLib` (or per-module) → catch non-compiling manifest entries (pattern 3).
4. Cross-check `scripts/flagship_axioms.txt` and `scripts/residual_axioms.txt` against the tree:
   every "flagship" must be `sorryAx`-free; every residual `axiom` must be allowlisted and owe an
   open issue.

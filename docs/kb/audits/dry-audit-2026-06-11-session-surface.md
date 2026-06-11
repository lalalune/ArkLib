# DRY / unification audit — 2026-06-10/11 campaign surface

Systematic duplication and symmetry audit over the files landed in the #329/#334/#340
campaigns, plus the pre-existing surfaces they touch. Each item: the duplication, the
consolidation, and its status.

## Consolidated this pass

1. **`ProximityGap.exists_dual_ne_zero` duplicated Mathlib** — Mathlib's
   `Module.Projective.exists_dual_ne_zero` (`LinearAlgebra/Dual/Lemmas.lean`) proves the same
   fact for projective modules (vector spaces are free hence projective); my basis-coordinate
   proof was a re-derivation. **Done**: the ArkLib lemma is now a thin wrapper (kept for the
   `A →ₗ[F] F` spelling its consumer `eq_zero_of_curve_agree_many` uses).

## Already-DRY by construction (the campaign's positive symmetries)

2. **`SubspaceAvoidance` as the shared counting engine** — one file serves: the #329 RLC
   kernel leaf (codim-1 count), [Jo26] Thm 4.2's avoidance/averaging (#334 K1/K2), the
   `A(q,s)` sharpness certificate (A2), and Thm 5.8's per-`V_T` capacity bound. Four
   consumers, zero clones.
3. **`curveExplainSubmodule_ne_top_of_no_witness`** — the standard-basis properness argument
   extracted once (`GG25WeightedTransfer.lean`) and shared by Theorems 5.7 and 5.8 (5.7's
   inline copy predates the extraction; see item 6).
4. **`curve_through_values`** (module-valued Lagrange) — built for Lemma 5.2, deliberately
   shaped for the planned `V_T`-style constructions; submodule-span membership is part of the
   statement so consumers never re-derive coefficient membership.
5. **Theorem 5.5's converse welds bricks 2/3/4** — no new machinery; the far-codeword
   close-set pinning reuses Lemma 5.4 exactly where a fresh argument would have duplicated
   its instance construction.

## Documented refactor debt (import-order or ownership constraints)

6. **Thm 5.7's inline properness block** — **DONE** (second pass): the lemma now lives in
   `GG25ExactPreservation.lean` and both 5.7 and 5.8 consume it; the ~40-line inline clone is
   deleted. Both files rebuild axiom-clean.
7. **`relationRound_last_iff` deg-3 vs deg-generic** — **DONE** (third pass): the generic
   moved into `TightMidLeaves.lean`; the deg-3 form is a one-line corollary; duplicate proof
   deleted; full downstream cone rebuilds clean.
8. **The `sfx*` direction facts cloned 3×** — **CAMPAIGN FILES DONE** (fourth pass): public
   `SpartanDirFacts.lean` extracted; both campaign clones deleted
   (`TightComposedCompleteness.lean` + `TightComposedFull.lean`, 34 call sites renamed); the
   full apex cone rebuilds axiom-clean against one copy. Sole remaining copy:
   `ComposedCompleteness.lean`'s original private block (sibling-shared — coordinate before
   editing; zero drift risk meanwhile since nothing else clones it).
9. **Inline `⊥ ≠ ⊤` proofs** — **DONE** (third pass): both sites now use
   `haveI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩; exact bot_ne_top` (Mathlib's lattice lemma; the
   `Nontrivial (Submodule F (Fin s → F))` instance synthesizes through `Function.nontrivial`).
10. **The 6-phase vs 8-phase chains** — **DONE** (third pass): deprecation-by-docstring
    landed on `ComposedTightRbrKnowledge.lean`, pointing new consumers at the apex pair.

## Method note

The census-wave triage (#337–#347) repeatedly found duplication's *audit-side* twin: residual
Props whose discharges exist under different names. The same root cause — name-based search
missing semantic identity — drives both. The docstring/tree-first rule
(`docs/wiki/append-residuals-and-elaboration-patterns.md`) is the countermeasure on the audit
side; this file is the countermeasure on the proof side.

# wf407 / B2-curve — curve-decodability ([GG25] Def 3.1) ↔ curve `ε_mca` seam

**Date:** 2026-06-14 · **Verdict:** PARTIAL (concrete bricks landed; δ* core unaffected).
**Honesty contract held — no fabricated closure.**

## TL;DR

The B2 lane ("[GG25] Def 3.1 curve decodability from scratch + its connection to ε_mca") is
**much further along than the `Frontier/CurveDecodability.lean` `example : True` stub suggests.**
The definition and the whole [Jo26] §5 transfer machinery are already landed and axiom-clean.
What was genuinely missing — and what this wave adds — is the **seam connecting the GG25
curve-decodability objects to the curve MCA error object `epsMCACurve`** (the prize-relevant
`ε_mca`). I landed that seam, axiom-clean, after pinning the exact logic with two exhaustive
(non-sampled) probes.

## What was already in tree (do NOT re-do)

| object | file | status |
|---|---|---|
| `def CurveDecodable` ([GG25] Def 3.1 / [Jo26] Def 2.7), `curveCloseSet`, mono, non-vacuity | `GG25CurveDecodability.lean` | axiom-clean |
| [Jo26] §5 marked variant, interleaving transfer (Thm 5.7), Lemma 5.2 interpolation, Thm 5.5 ⟺ | `CurveDecodability.lean` (`ProximityGap.CurveDec`) | axiom-clean |
| [GG25] Thm 3.3: curve-decodability ⟹ all-seeds-close (MCA spread, both integer + relative form) | `GG25MCAFromCurveDecodability.lean` | axiom-clean |
| curve MCA error `mcaEventCurve` / `epsMCACurve`, `epsMCACurve_two_eq_epsMCA` (L=2 ↦ line) | `MCACurveEvent.lean` | axiom-clean |
| `GG25{MarkedCurve,ExactPreservation,NonCovering,SmallWitness,SpreadBound,WeightedTransfer,MarkedEquivalence}` | each file | axiom-clean (no `sorry` tokens) |

The `Frontier/CurveDecodability.lean` `example : True` is a **leftover scaffold**, not the lane
(canonical declarations: `git grep -il curvedecodab`). I updated its docstring to a pointer map.

## The gap I closed

`CurveDecodable` (over the close set of **seeds** `α ∈ F`) and `mcaEventCurve` (a **per-seed**
bad event about the **rows** of the tested stack) were both defined but **no theorem connected
them.** I added the seam in `Frontier/WF407_B2-curve.lean` (namespace `ProximityGap.WF407B2`):

1. `not_mcaEventCurve_iff_stackAgrees` — **the negation characterization.** `mcaEventCurve C δ u γ`
   fails iff *every* large (`≥ (1−δ)n`) curve-close witness set admits a jointly-agreeing
   codeword stack. The exact statement of the obstruction the event encodes.
2. `mcaEventCurve_false_of_rows_mem` — **codeword stacks are MCA-clean.** If every row of `u`
   is a codeword, `mcaEventCurve C δ u γ` is false for every seed `γ`, every radius `δ`.
3. `epsMCACurve_term_codewordStack_eq_zero` — the per-stack probability `Pr_γ[mcaEventCurve]`
   is `0` on codeword stacks (the `epsMCACurve` supremum's worst case is never a codeword stack).
4. `not_mcaEventCurve_of_full_stackAgrees` — **the curve-decodability-facing sufficient
   condition.** A tested stack jointly agreeing with a codeword stack on all of `ι` has no MCA
   event — the form a curve-decodability conclusion takes (it produces the single explaining
   codeword stack).
5. `mcaEventCurve_imp_witness` — packaged contrapositive for downstream consumers.

Axiom audit (pg-iterate, real `lake env lean`, exit 0, 262s): all six report
`[propext, Classical.choice, Quot.sound]` (one tighter — no `Classical.choice`). No `sorryAx`,
no `native_decide`.

## Exact numerical evidence (non-sampled)

`scripts/probes/wf407_B2-curve_{bridge,epsmca}.py` (q=5, n=4, k=2 RS-like, brute-force):

* **codeword stacks ⟹ no MCA event: `0/9375` violations** (δ ∈ {1/4,1/2,3/4}, all γ, all
  codeword stacks) — verifies brick (2)/(3).
* **the bad event is genuinely non-trivial**: a non-codeword stack achieves `4/5` bad seeds at
  δ=1/4, and `mcaEventCurve` witnesses exist (curve δ-close to a codeword while **no** codeword
  stack agrees rowwise) — confirms we must NOT claim "curve δ-close ⟹ no MCA event" (FALSE);
  the seam only gives the codeword-stack / full-agreement directions, which are the true ones.

## What remains open (the δ* core — unchanged)

The *quantitative* `epsMCACurve` upper bound for **explicit smooth-domain plain RS** in the
prize window `(1−√ρ, 1−ρ−Θ(1/log n))` at `ε*=2^-128`. [GG25] supplies curve-decodability only
for folded-RS / multiplicity / random-RS / subspace-design codes — not the explicit plain RS the
prize fixes. The spread direction (Thm 3.3) is landed; the missing input is the sub-√q
list-size / Gauss-period wall (the master open core, faces 1–4 in `UNFINISHED_THREADS_407.md`).
This lane does not touch that core; it makes the *definitional* connection precise and clean.

## Artifacts

* `ArkLib/Data/CodingTheory/ProximityGap/Frontier/WF407_B2-curve.lean` (6 axiom-clean thms)
* `scripts/probes/wf407_B2-curve_bridge.py`, `scripts/probes/wf407_B2-curve_epsmca.py`
* `ArkLib/Data/CodingTheory/ProximityGap/Frontier/CurveDecodability.lean` (stub → pointer map)

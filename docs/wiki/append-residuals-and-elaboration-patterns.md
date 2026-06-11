# Append residuals & recurring Lean elaboration patterns

Status notes and reusable proof patterns from the 2026-06-10/11 campaign closing #329,
the [Jo26] program on #334, and the #340 residual audit. Cross-referenced from those issues.

## The append-composition residual map (#340)

Every named residual in `OracleReduction/Composition/Sequential/Append.lean` is in one of
three honest states:

1. **Conditionally discharged** — the residuals are *statement-gapped by design* (their
   docstrings say which side conditions are missing), so the conditional discharge is the
   honest endpoint. Message-seam: `AppendResidualDischarges.lean`. Challenge / failing-det /
   empty-trailing seams + the error-ful completeness pair:
   `AppendResidualDischargesSeams.lean`. All four proven keystone regimes discharge the
   rbr-KS residual.
2. **Reduced to a discharged counterpart** — the `OracleVerifier.*` mirrors transport to the
   `Verifier.*` discharges via `toVerifier`-commutation
   (`AppendKnowledgeOracleTransport.lean`, `AppendRbrSoundnessOracleLift.lean`,
   `AppendRbrKnowledgeOracleLift.lean`).
3. **Documented-obstructed** — `Verifier.appendKnowledgeSoundnessResidual` (plain
   straightline KS composition). Its docstring carries a *proven obstruction*: the phase-1
   bad event needs the extracted `wit₂ = E₂(phase-2 randomness)`, but a phase-1 prover has no
   oracle access to `pSpec₂`'s challenges — unstateable, not merely unproven; bites even at
   `Subsingleton σ`. **Do not attempt the direct two-stage extractor composition** (the
   "obvious" `P₁'` construction smuggles phase-2 randomness into the phase-1 game). The
   sanctioned route is round-by-round, which is discharged.

**Meta-rule learned three corrections deep: read the residual's full docstring before scoping
work on it.** The audit-visibility pattern (#337/#338/#340): residual `def : Prop`s often
have discharges under different names, or documented obstructions, that a grep for
`<name>_holds` misses.

## Recurring elaboration walls and their fixes

### `Finset.sum` vs pointwise Pi defeq (`whnf` divergence)

`∑ k, lam k • (fun i => f i k)` and `fun i => ∑ k, lam k • f i k` are definitionally equal
only through `Multiset.foldr` — `whnf` diverges trying. Symptom: `(deterministic) timeout at
whnf` at uses of hypotheses mixing the two shapes (membership in submodules, distance
arguments), *not* at their statement sites. Fix: never lean on the defeq; cross through an
explicit bridge once per shape mix:

```lean
have : rowCombine lam w = ∑ k, lam k • (fun i => w i k) := by
  funext i; rw [Finset.sum_apply]; exact Finset.sum_congr rfl fun k _ => rfl
```

(`ProximityGap.rowCombine_eq_sum_rows`, `GG25ExactPreservation.lean`, is the worked example —
the [Jo26] Theorem 5.7 assembly was blocked on exactly this.)

### Probe-bisection of elaboration walls

When a big proof hits unexplained `whnf`/instance timeouts: isolate single steps in tiny
`/tmp` probe files (hypothesis consumption alone, statement elaboration alone, one tactic at
a time) and *falsify* candidate culprits before rewriting anything. The Theorem 5.7 unblock
falsified four plausible hypotheses (interleave-notation projection, clause consumption,
statement elaboration, `push Not` through double-Pi filters — all instant in isolation)
before localizing the sum-defeq wall above.

### Other one-line gotchas (same campaign)

- `Basis.*` → `Module.Basis.*` (Mathlib rename); `div_le_div_iff` → `div_le_div_iff₀`.
- Mathlib's `Lagrange.eval_basis_*` are keyed on `eval (id β)` — insert
  `show … = eval (id β) … from rfl` casts.
- `dif_pos`/`dif_neg` under a lambda: `beta_reduce` first.
- Transporting `choose`-results across an embedding: `congr 1` closes the proof-irrelevant
  `Finset` equality where `subst` fails (the variable occurs in the `choose` term).
- `Function.Embedding.nonempty_of_card_le` + `Fintype.card_coe` + `card_powersetCard` is the
  junk-completion recipe for covering-lemma applications indexed by subsets.
- Generalizing a fold over a component: generalize the **conclusion** too, or the unifier
  diverges re-expanding the hardcoded chain (whnf timeout + a kernel self-reference artifact
  that mimics laundering but is an elaboration failure).

# Sequential-composition / append keystone — verified state (2026-06-08)

Audit of the `Prover.append_run` / `append_soundness` / `append_completeness` /
monad-commutation (#433) keystone that gates #114, #62, #13. Every claim below was
confirmed by reading source and/or `lake env lean` probing against the built
`Append.olean`.

## What is genuinely proven (sorry-free, axiom-clean)

Prover-side run factoring (`Append.lean`, `EmptyAppend.lean`):
- `Prover.append_run` — conditional on the syntactic residual `appendRunRightResidual`.
- `Prover.append_run_msg` — **unconditional** for a message-first seam
  (`pSpec₂.dir 0 = .P_to_V`); discharges the residual via `appendRunRightResidual_holds_msg`.
  This is a *syntactic* `OracleComp` equality: `(P₁.append P₂).run = P₁.run >>= P₂.run`
  (concatenating transcripts).
- `Prover.append_run_empty` — the `n = 0` analogue.
- `Prover.append_run_evalDist` / `append_run_evalDist_msg` (`AppendRunEvalDist.lean`) — the
  distribution-level factoring; unconditional for the message seam, uses `evalDist_bind_comm`
  only for the challenge seam.

Malicious-prover seam decomposition (`SeamDecomposition.lean`, `SeamDecompositionRun.lean`):
- `Prover.fst` / `Prover.snd` — split an arbitrary prover over `pSpec₁ ++ₚ pSpec₂` at the seam.
- `merge_run`, `run_seam_factor` — `P.run = (fst P).run >>= (snd P).run` (message seam).

Verifier side: `Verifier.append_run` is `rfl`.

## What is open (residual-gated `def : Prop` stubs — NOT proofs)

Every `*_append_completeness` / `append_soundness` / `append_knowledgeSoundness` /
`append_rbr*` in `Append.lean` is stated honestly but proved by `hResidual`, where the
hypothesis `hResidual : <named residual>` is **definitionally the goal itself**
(`appendSoundnessResidual V₁ V₂ h₁ h₂ := (V₁.append V₂).soundness …`). These are
placeholders, not closures. Likewise `AppendPerfectCompleteness.lean`'s
`append_perfectCompleteness_msg` is a `def … : Prop`, not a theorem.

## The remaining mathematical content

`Reduction.run` (Execution.lean:174) runs prover then verifier; the appended run orders
`P₁, P₂, V₁, V₂` while the sequential `R₁.run >>= R₂.run` orders `P₁, V₁, P₂, V₂`. A
*distribution* identity would need to commute `V₁` past `P₂` (the #433 monad commutation).
**Perfect completeness only needs support containment**, which is order-insensitive
(`probEvent_eq_one_iff` + `mem_support_bind_iff`), so the assembly avoids commutation.
Worked plumbing template for the `Pr[· | OptionT.mk (simulateQ pImpl …).run' (← init)] = 1`
shape: `Reduction.id_perfectCompleteness` (Security/Basic.lean:585).

### Shared crux: the challenge-oracle seam bridge

Both the completeness and soundness assemblies need to apply the per-phase hypotheses
`h₁`/`h₂`, which simulate over the *component* challenge oracles `[pSpecᵢ.Challenge]ₒ`,
whereas the appended run's lifted sub-runs route challenge queries through the *combined*
`[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`. The bridge to prove (left half; right half symmetric):

```lean
simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁ ++ₚ pSpec₂)))
    (liftM oa : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) α)
  = simulateQ (impl.addLift (challengeQueryImpl (pSpec := pSpec₁))) oa
-- oa : OracleComp (oSpec + [pSpec₁.Challenge]ₒ) α
```

Verified reduction path (via `QueryImpl.simulateQ_liftM_eq_of_query`, two per-query goals):
- **inl (oSpec query): SOLVED.** Collapse the outer lift with `OracleComp.liftComp_query`,
  then `rw [simulateQ_spec_query]; rfl` (`QueryImpl.add_apply_inl`).
- **inr (challenge query): reduced to a `$ᵗ` congruence across the seam.** After
  `liftComp_query` + `OracleQuery.liftM_right_add_right_add_query` the goal becomes
  `(range_challenge_append_inl ▸ ·) <$> $ᵗ((pSpec₁ ++ₚ pSpec₂).Challenge (inl t.1))
   = $ᵗ(pSpec₁.Challenge t.1)`. This holds **without** invoking uniqueness-of-uniform
  because the combined `SampleableType` instance is `Fin.fappend₂`-derived
  (`SeqCompose.lean:392`) and reduces to the `pSpec₁` instance at `inl` indices — the type
  and the instance cohere. Remaining work: route the `OracleQuery chal_comb → OracleComp`
  lift to expose `simulateQ_query`, then discharge the `Fin.fappend₂`/`ChallengeIdx.inl`
  cast (mechanical but several `rfl`-routing rewrites; not yet closed).

Crucial subtlety confirmed by probing: the seam challenge types
`(pSpec₁ ++ₚ pSpec₂).Challenge (inl i)` and `pSpec₁.Challenge i` are only *propositionally*
equal (rfl fails), and even with the synthesized `Fin.fappend₂` instance the samplers are not
defeq across the cast. So a **computation-level** bridge (via `simulateQ_liftM_eq_of_query`)
is the wrong target — it would demand the two `selectElem`s be equal as computations.

**Correct framing: state the bridge at `evalDist` level**, matching how completeness/soundness
actually consume it (cf. the proven `append_run_evalDist`). Then the inr per-query goal is
`evalDist ((cast ▸) <$> $ᵗ A) = evalDist ($ᵗ B)` — **uniqueness of the uniform
distribution**, which IS provable from the `SampleableType` axioms
(`probOutput_selectElem_eq` + `mem_support_selectElem`) via `evalDist_ext`. Confirmed the
route typechecks (`evalDist_ext; intro x; …`), remaining is the `Pr[=x] = 1/card` pinning.

Two atomic sub-lemmas isolated:
- **Atom 1 (PROVEN):** `f <$> (liftM x : StateT σ ProbComp _) = liftM (f <$> x)` by
  `simp only [map_eq_pure_bind, liftM_bind, liftM_pure]`.
- **Atom 2 (PROVEN):** uniform transport across the seam type equality —
  `evalDist (cast h <$> uniformSample A) = evalDist (uniformSample B)` for `h : A = B`,
  `[Finite A]`, by `evalDist_ext; intro y; exact
  probOutput_map_bijective_uniform_cross (α := A) (β := B) (cast h) (cast_bijective h) y`.
  (The vcvio lemma `probOutput_map_bijective_uniform_cross` is exactly uniqueness-of-uniform
  pushed along a bijection; the cast is bijective.) No never-fail hypothesis needed — it is
  baked into `probOutput_uniformSample`/`sum_probOutput_eq_one`.

Both atoms + the inl case are machine-checked (scratch `lake env lean`, against `Append.olean`).
The bridge then assembles at evalDist/support level (NOT computation level — the challenge case
is only a distributional equality). For *perfect* completeness the support route is even lighter:
the challenge sampler has full support on both (equal) types, so
`support (simulateQ pImpl_comb (liftM oa)) = support (simulateQ pImpl₁ oa)` holds with
`mem_support_selectElem` alone.

### After the bridge

Completeness: support-decompose the appended `Reduction.run` (rewrite prover via the
syntactic `append_run_msg`, verifier via `Verifier.append_run`), pull the four sub-supports
with `mem_support_bind_iff` through the `simulateQ`/`StateT.run'`/`OptionT` layers, apply
`h₁` (pins `V₁`'s output to `P₁`'s `s₂ ∈ rel₂`) then `h₂` (lands in `rel₃`).
Soundness: same seam split via `run_seam_factor`, then a two-event union bound through the
intermediate statement `stmt₂`.

## Bottom line

The prover-side keystone is done. The open work is the Reduction/Verifier-level assembly,
whose single shared deep ingredient is the challenge-oracle seam bridge above (inl half
proven; inr half reduced to a mechanical fappend cast). This is a multi-session
formalization; the residual `def : Prop` stubs are the honest gap markers and must not be
collapsed to tautologies.

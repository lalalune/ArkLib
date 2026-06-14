# OptionT lift-coherence walls: the per-branch-defeq technique

Status: stable technique, proven in `ArkLib/OracleReduction/FiatShamir/RunEqHonestExecution.lean`
(the discharge of `fiatShamir_runCollapseResidual`). Maintained per the wiki rules in
[`README.md`](README.md).

## The problem

Run-unrolling proofs (Fiat-Shamir transforms, append seams, simulated executions) routinely
get stuck on equalities whose two sides *display identically* but do not close under `rfl`,
`simp`, `rw`, `bind_congr`, or even `with_unfolding_all rfl`:

```
⊢ (liftM X).run = (liftM X).run
```

The cause is **instance-path divergence**: the same source computation is lifted along two
different `MonadLiftT` composites — e.g. the *two-step associativity-routed* path
`OracleComp base → OptionT (OracleComp base) → OptionT (OracleComp doubled)` chosen by a
`run` unrolling, versus the *direct* path `OracleComp base → OracleComp doubled →
OptionT (OracleComp doubled)` a fresh elaboration picks. The composites are propositionally
equal but not definitionally, and every congruence tactic that needs syntactic head
unification fails. Several named residuals document exactly this wall ("the OptionT
lift-coherence bridge between the two-step associativity-routed lift chosen by `run` and the
direct lift").

## The technique

1. **Unroll the shell** with the protocol's `run_of_prover_first` / `*_run_eq_oneMessage`
   specialization plus the transform-projection `simp only` set
   (`Reduction.<transform>`, `Prover.<transform>`, `Verifier.<transform>`, `Verifier.run`,
   the `*_verify_eq` lemma, `liftM_bind`, `liftM_pure`, `bind_assoc`, `pure_bind`,
   `OptionT.run_bind`).
2. **Collapse `getM` walls** with `OptionT.liftM_run_getM_bind` (`ArkLib/ToVCVio/Simulation`)
   and `lift_run_elim` (namespace `OptionTStateT`, `ArkLib/OracleReduction/RunUnroll`).
3. **Go to run level**: `apply OptionT.ext`, then
   `simp only [OptionT.run_bind, OptionT.run_lift, OptionT.run_liftM_run,
   OracleComp.liftM_OptionT_eq, OptionT.run_pure, map_eq_bind_pure_comp, …]`.
4. **Bridge each coherence square by induction with per-`Sum`-branch defeq.** This is the
   key move. State the bridge (`simulateQ`-of-routing = `liftM`; annotated-path =
   direct-path — the annotated `@liftM … (instMonadLiftTOfMonadLift …)` form IS spellable)
   and prove it by `OracleComp.inductionOn`:
   - `pure`: `rfl` or `(liftM_pure _).symm`;
   - `query_bind`: `rcases t with t₁ | t₂ <;> (simp only [liftM_bind]; exact
     bind_congr fun a => ih a)`.

   The instance paths differ *globally* but agree *on each routed query constructor*, so the
   per-branch goals are definitional even though the unsplit goal is not.
5. **Dodge lambda-instance mismatches by generalizing the impl**: where a bridge must match a
   `simulateQ (fun t => liftM (query t)) …` occurrence inside the goal, do not state the
   bridge with your own elaboration of that lambda (it will not match). Take the impl as a
   variable plus a pointwise hypothesis `himpl : ∀ t, impl t = liftM (query t)` and
   discharge `himpl` at the use site with `fun t => by with_unfolding_all rfl`.
6. **Descend the `Option.elim` cascade** with `apply bind_congr; intro d; rcases d with
   _ | d; · rfl`, inserting `simp only [Option.elim]` after `some`-branches. Where heads
   differ by a bridged square, use
   `refine Eq.trans (congrArg₂ (· >>= ·) (congrArg (fun Y => OptionT.run (liftM Y))
   (<bridge> …)) rfl) ?_` followed by `beta_reduce`. Close Option-nesting tails with
   `rcases … <;> rfl`.

## Anti-patterns

- **`congr 1` on the cascade**: it fractures into instance-`HEq` and type-level goals
  (`d = Option d`) that are unprovable noise. Use `bind_congr` descent instead.
- **An explicit `[∀ i, SampleableType ((p₁ ++ₚ p₂).Challenge i)]` binder**: it fights the
  canonical derived instance and whnf-explodes engine applications. Let the global instance
  derive it.
- **Instantiating big engines at literal `ProtocolSpec 0`**: state at generic `n` with
  `(hn0 : n = 0)` and `subst` only inside the leg that needs it.
- **Trusting `first | rfl | …` probes**: a `by`-block inside `congrArg₂` with metavariable
  endpoints will self-unify (`rfl` proving `x = x` with the meta set to the LHS) and change
  nothing. Pin both sides with `show`-spelled forms before the tactic.

## The duplex-sponge wall (solved)

The DS analogues initially resisted every step above. The resolution
(`Security/LiftCoherence.lean`, `dsfs_hLHS`) exposed two further lessons:

- **Spell the TRUE mid-spec.** The annotated two-step path's intermediate monad is the
  assoc-*nested* sum (`oSpec + (dsCh + [Chal]ₒ)`), not `OptionT` over the base. With the
  `instMonadLiftTOfMonadLift` annotation spelled against the real path (discover it with a
  `pp.explicit` `#print` of a wrapper def), the induction's query case collapses to one
  `simp only [liftM_bind]` — weeks of apparent tower-depth was a wrong annotation.
- **Instance diamonds through structured oracles.** Query routes can resolve *through* an
  oracle's internal domain sum (`duplexSpongeChallengeOracle`'s
  `StmtIn ⊕ (SpongeState ⊕ SpongeState)`) rather than treating it atomically, producing
  extensionally-equal-but-syntactically-foreign routes that no structural `@[simp]` routing
  lemma matches. Close them by case analysis over the *internal* domain
  (`rcases t₂ with s | (c | c) <;> rfl`).

`OracleComp.simulateQ_simulateQ` (`ToVCVio/Simulation.lean`) collapses genuine
`simulateQ` towers when they do appear. Pure-`rfl` run-characterizations of composite
`OptionT` lifts (`optionT_liftM_run_add_left'`, `optionT_liftM_run_assoc_path'`) pin the
`Eq.trans (b := …) ?_ (by rfl)` descent anchors.

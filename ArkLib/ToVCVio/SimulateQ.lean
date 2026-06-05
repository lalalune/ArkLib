/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.OracleComp.SimSemantics.Append

/-!
# `simulateQ` over `forIn` and three-way `addLift` (staged for upstream to VCVio)

Additions to VCVio's `simulateQ` simp set that ArkLib needs but that the
currently-pinned VCVio commit predates. They are *staged* here so they can be
deleted wholesale once the VCVio dependency is bumped — see
`ArkLib/ToVCVio/README.md`.

* `simulateQ_list_forIn` — a monad morphism commutes with `forIn` on a list
  (the `forIn` sibling of VCVio's `simulateQ_list_mapM` / `simulateQ_list_forM`).
  This is the lemma that lets a `simulateQ` in front of a verifier spot-check
  loop `for j in List.finRange t do …` move inside the loop body. It is already
  upstreamed to VCVio under the same name; this copy duplicates it verbatim only
  because ArkLib pins an earlier VCVio commit.

* `simulateQ_addLift_add_liftM_left` / `simulateQ_addLift_add_liftM_right` —
  resolve a `simulateQ` over a *three-way* `addLift impl (impl₁ + impl₂)` applied
  to a computation that was double-`liftM`'d from one of the two inner oracle
  families. This is the shape produced by an `OracleVerifier`'s
  `simOracle2`-routed query helpers (a query over `[OStmt]ₒ` or `[Message]ₒ`,
  lifted into `[OStmt]ₒ + [Message]ₒ`, then into `oSpec + (…)`). The existing
  `QueryImpl.simulateQ_add_liftComp_{left,right}` simp lemmas only peel a *single*
  `addLift` layer; these compose two peels with `simulateQ_liftTarget` so the
  query routes to the correct inner implementation in one step.
-/

open OracleComp OracleSpec

/-- `simulateQ` distributes over `forIn` on a list: a monad morphism commutes
with `forIn`. Proved by list induction via `List.forIn_cons` + `simulateQ_bind`,
casing on the `ForInStep` accumulator. (Verbatim copy of the upstream VCVio
lemma; delete on the next VCVio bump.) -/
@[simp]
lemma simulateQ_list_forIn {ι : Type*} {spec : OracleSpec ι} {n : Type → Type _}
    [Monad n] [LawfulMonad n] (impl : QueryImpl spec n) {α β : Type}
    (xs : List α) (init : β) (f : α → β → OracleComp spec (ForInStep β)) :
    simulateQ impl (forIn xs init f) = forIn xs init (fun a b ↦ simulateQ impl (f a b)) := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons, simulateQ_bind]
    congr 1
    funext step
    cases step with
    | done b => simp
    | yield b => exact ih b

/-- Resolve a `simulateQ` over a three-way `addLift impl (impl₁ + impl₂)` applied to a
computation `x : OracleComp spec₁ α` that has been double-`liftM`'d — first into the inner
sum `spec₁ + spec₂`, then into the outer sum `spec + (spec₁ + spec₂)`. The query routes to
the *left* inner implementation `impl₁`, leaving `liftM (simulateQ impl₁ x)`.

This is the `left` half of the `simOracle2`-routing pair: it peels the outer `addLift`
(`simulateQ_add_liftComp_right`), commutes the inner `simulateQ` past the target lift
(`simulateQ_liftTarget`), then peels the inner sum (`simulateQ_add_liftComp_left`). Stated
for the inner pair living in a possibly-different monad `n` lifted into the target `m`
(as `simOracle2`'s `Id`-valued `simOracle0`s are). -/
lemma simulateQ_addLift_add_liftM_left
    {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {n : Type → Type} [Monad n] [LawfulMonad n] [MonadLiftT n m] [LawfulMonadLiftT n m]
    (impl : QueryImpl spec m) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    {α : Type} (x : OracleComp spec₁ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)
        : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (liftM x : OracleComp (spec₁ + spec₂) α) : OracleComp (spec + (spec₁ + spec₂)) α)
      = (liftM (simulateQ impl₁ x) : m α) := by
  rw [show QueryImpl.add impl₁ impl₂ = impl₁ + impl₂ from rfl,
    ← OracleComp.liftComp_eq_liftM, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
    simulateQ_liftTarget, QueryImpl.simulateQ_add_liftComp_left]

/-- Resolve a `simulateQ` over a three-way `addLift impl (impl₁ + impl₂)` applied to a
computation `x : OracleComp spec₂ α` that has been double-`liftM`'d — first into the inner
sum `spec₁ + spec₂`, then into the outer sum `spec + (spec₁ + spec₂)`. The query routes to
the *right* inner implementation `impl₂`, leaving `liftM (simulateQ impl₂ x)`.

The `right` companion of `simulateQ_addLift_add_liftM_left`; see that lemma for the
`simOracle2` motivation. -/
lemma simulateQ_addLift_add_liftM_right
    {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    {m : Type → Type} [Monad m] [LawfulMonad m]
    {n : Type → Type} [Monad n] [LawfulMonad n] [MonadLiftT n m] [LawfulMonadLiftT n m]
    (impl : QueryImpl spec m) (impl₁ : QueryImpl spec₁ n) (impl₂ : QueryImpl spec₂ n)
    {α : Type} (x : OracleComp spec₂ α) :
    simulateQ (QueryImpl.addLift impl (QueryImpl.add impl₁ impl₂)
        : QueryImpl (spec + (spec₁ + spec₂)) m)
      (liftM (liftM x : OracleComp (spec₁ + spec₂) α) : OracleComp (spec + (spec₁ + spec₂)) α)
      = (liftM (simulateQ impl₂ x) : m α) := by
  rw [show QueryImpl.add impl₁ impl₂ = impl₁ + impl₂ from rfl,
    ← OracleComp.liftComp_eq_liftM, ← OracleComp.liftComp_eq_liftM,
    QueryImpl.addLift_def, QueryImpl.simulateQ_add_liftComp_right,
    simulateQ_liftTarget, QueryImpl.simulateQ_add_liftComp_right]

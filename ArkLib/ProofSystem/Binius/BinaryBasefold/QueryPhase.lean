/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec

namespace Binius.BinaryBasefold.QueryPhase

/-!
## Query Phase (Final Query Round)
The final verification phase (proximity testing) as an oracle reduction.
(Note that here `B_k` means the boolean hypercube of dimension `k`)

- `V` executes the following querying procedure:
  for `γ` repetitions do
    `V` samples a challenge `v ← B_{ℓ+R}` randomly and sends it to P.
    for `i in {0, ϑ, ..., ℓ-ϑ}` (i.e., taking `ϑ`-sized steps) do
      for each `u` in `B_v`, => gather data for `c_{i+ϑ}`
        `V` sends (query, [f^(i)], (u_0, ..., u_{ϑ-1}, v_{i+ϑ}, ..., v_{ℓ+R-1})) to the oracle.
      if `i > 0` then `V` requires `c_i ?= f^(i)(v_i, ..., v_{ℓ+R-1})`.
      `V` defines `c_{i+ϑ} := fold(f^(i), r'_i, ..., r'_{i+ϑ-1})(v_{i+ϑ}, ..., v_{ℓ+R-1})`.
    `V` requires `c_ℓ ?= c`.
-/
noncomputable section
open OracleSpec OracleComp
open AdditiveNTT Polynomial MvPolynomial

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal

/-!
## Generic `forIn`-loop support theory  (candidate for upstreaming to VCVio)

The verifier `verify` body below is a doubly-nested `List.forIn` with early-exit
`unless … do return false` branches. Computing the `support` of such a loop requires pushing
`support` through `forIn`, for which neither VCVio, Mathlib, nor ArkLib provides a lemma
(`simulateQ_bind` does not apply — `forIn` is a recursor, not a `bind`; and the only existing
bridge `List.forIn_mprod_yield_eq_foldlM` is yield-only, rejecting the early-exit).

The transport layer here is built on the core unfolding equations `List.forIn_nil` /
`List.forIn_cons` (already in Lean core) together with the generic `support_bind` /
`mem_support_bind_iff` / `support_pure` API (available for any `HasEvalSet m`). The two workhorses
are:

* `mem_support_forIn_cons` — a clean membership characterization for the cons-step support, and
* `forIn_support_invariant` — an induction-free invariant rule: a predicate preserved by every
  per-element step (over the body's support) holds of every value in the loop's support.

A third lemma, `forIn_yield_pure_eq_foldl`, collapses an all-`yield` `pure`-bodied loop to a `pure`
of a left fold; this is the shape an early-return loop takes once every check is known to pass
(the `do`-notation early-return desugaring threads an `Option`-flagged accumulator, and under
"all checks pass" the body never emits a `done`, so the loop reduces to a deterministic fold).

These lemmas are protocol-agnostic (any `HasEvalSet` monad — in particular the `OptionT (OracleComp
…)` of an `OracleVerifier.verify` body and its `simulateQ`-image) and are candidates for upstreaming
to VCVio's loop/distribution theory.
-/
namespace ForInSupport

variable {m : Type → Type} [Monad m] [LawfulMonad m] [HasEvalSet m] {α γ : Type}

omit [LawfulMonad m] in
/-- Membership characterization of the support of `forIn (a :: l) init f`: a value `x` is reachable
iff there is a first-step `step` in the body's support such that, on `done b`, `x = b`, and on
`yield b`, `x` is reachable from the tail loop started at `b`. -/
theorem mem_support_forIn_cons (a : α) (l : List α) (init : γ)
    (f : α → γ → m (ForInStep γ)) (x : γ) :
    x ∈ support (forIn (a :: l) init f) ↔
      ∃ step ∈ support (f a init),
        (match step with
          | .done b => x = b
          | .yield b => x ∈ support (forIn l b f)) := by
  rw [List.forIn_cons, mem_support_bind_iff]
  constructor
  · rintro ⟨step, hstep, hx⟩
    refine ⟨step, hstep, ?_⟩
    cases step with
    | done b => rw [mem_support_pure_iff] at hx; exact hx
    | yield b => exact hx
  · rintro ⟨step, hstep, hx⟩
    refine ⟨step, hstep, ?_⟩
    cases step with
    | done b => rw [mem_support_pure_iff]; exact hx
    | yield b => exact hx

omit [LawfulMonad m] in
/-- **Invariant rule for `forIn`-loop support.** If `Inv` holds of the initial accumulator and is
preserved by every per-element step (over the support of the body), then `Inv` holds of every value
in the support of the whole loop. This is the structural workhorse for transporting per-iteration
facts (e.g. "this consistency check passed") out of the support of a loop-based verifier run. -/
theorem forIn_support_invariant (Inv : γ → Prop) (l : List α)
    (f : α → γ → m (ForInStep γ))
    (hstep : ∀ a ∈ l, ∀ b, Inv b → ∀ step ∈ support (f a b), Inv step.value) :
    ∀ init, Inv init → ∀ x ∈ support (forIn l init f), Inv x := by
  induction l with
  | nil =>
    intro init hinit x hx
    rw [List.forIn_nil, mem_support_pure_iff] at hx
    exact hx ▸ hinit
  | cons a l ih =>
    intro init hinit x hx
    rw [mem_support_forIn_cons] at hx
    obtain ⟨step, hstepmem, hx⟩ := hx
    have hInvStep : Inv step.value := hstep a (List.mem_cons_self) init hinit step hstepmem
    cases step with
    | done b => simp only at hx; exact hx ▸ hInvStep
    | yield b =>
      simp only at hx
      exact ih (fun a' ha' => hstep a' (List.mem_cons_of_mem _ ha')) b hInvStep x hx

omit [HasEvalSet m] in
/-- **All-`yield` collapse.** A loop whose body always `pure`s a `yield` with new state `g a b`
collapses to a deterministic `pure` of the left fold of `g` over the list. This is the value an
early-return loop assumes once every check is known to pass: the `done` branches are never taken,
so the whole loop is a pure fold (used to evaluate the honest verifier run for completeness). -/
theorem forIn_yield_pure_eq_foldl (l : List α) (g : α → γ → γ) :
    ∀ init : γ,
      (forIn l init (fun a b => (pure (ForInStep.yield (g a b)) : m (ForInStep γ))))
        = pure (l.foldl (fun b a => g a b) init) := by
  induction l with
  | nil => intro init; rw [List.forIn_nil]; rfl
  | cons a l ih =>
    intro init
    rw [List.forIn_cons]
    simp only [pure_bind]
    rw [ih (g a init)]
    rfl

/-! ### `StateT.run`-evaluated `forIn` support theory  (`OptionT (StateT σ ProbComp)`)

The verifier `verify` body, once its oracle queries are collapsed by `simulateQ`, is a doubly-nested
`forIn` over the transformer stack `OptionT (StateT σ ProbComp)`. The generic
`forIn_support_invariant` above is stated for any `[HasEvalSet m]`, but `HasEvalSet (StateT σ ProbComp)`
is **not** available (probability `support` lives at the `ProbComp` level, reached only after
`StateT.run … s`). So the loop's support must be analyzed *after* evaluating the `StateT` at the
initial state `s`. The two lemmas below supply exactly that transport: they push `StateT.run` through
a `forIn` cons-step (landing at the `ProbComp` level, where `support` and `mem_support_bind_iff`
apply) and lift it to an induction-free invariant rule. This is the missing
`StateT.run`-through-`forIn` bridge that lets a per-iteration fact (e.g. "no early `done` exit") be
transported out of the support of the loop-based, `simulateQ`-collapsed verifier run. -/

/-- **`StateT.run`-evaluated `forIn` cons-step membership.** Membership in the support of the
`StateT.run … s`-evaluation of `forIn (a :: l) init f` (an `OptionT (StateT σ ProbComp)` loop)
decomposes into a first-step outcome `p` in the support of `StateT.run (f a init) st`, followed by the
remaining loop run on `p`'s `yield`/`done`/`none` branch. Proved by reducing the `OptionT`/`StateT`
bind to a `ProbComp`-level bind (`List.forIn_cons` + the monad-instance unfolds) and applying
`mem_support_bind_iff`. -/
theorem stateT_run_forIn_cons_mem {σ' δ ε : Type} (a : ε) (l : List ε) (init : δ)
    (f : ε → δ → OptionT (StateT σ' ProbComp) (ForInStep δ)) (st : σ') (x : Option δ × σ') :
    x ∈ support (StateT.run (forIn (a :: l) init f : OptionT (StateT σ' ProbComp) δ) st) ↔
      ∃ p ∈ support (StateT.run (f a init) st),
        x ∈ support
          (match p.1 with
            | some (ForInStep.done b) => StateT.run (pure b : OptionT (StateT σ' ProbComp) δ) p.2
            | some (ForInStep.yield b) =>
                StateT.run (forIn l b f : OptionT (StateT σ' ProbComp) δ) p.2
            | none => (pure (none, p.2) : ProbComp (Option δ × σ'))) := by
  rw [List.forIn_cons]
  simp only [bind, OptionT.bind, OptionT.mk, StateT.bind, StateT.run]
  erw [mem_support_bind_iff]
  apply exists_congr; intro p
  apply and_congr_right; intro _
  rcases p with ⟨op, sp⟩
  rcases op with _ | step
  · rfl
  · rcases step with b | b <;> rfl

/-- **Invariant rule for the `StateT.run`-evaluated `forIn`-loop support.** If `Inv` holds of the
initial accumulator and is preserved by every per-element body step (over the support of the
`StateT.run`-evaluated body, looking at the `yield`/`done` outcome's accumulator), then `Inv` holds of
every successful (`some`-tagged) accumulator value in the support of the whole evaluated loop. This is
the `OptionT (StateT σ ProbComp)` analogue of `forIn_support_invariant`, usable on the
`simulateQ`-collapsed verifier run where `support` is only available post-`StateT.run`. -/
theorem stateT_run_forIn_support_invariant {σ' δ ε : Type}
    (Inv : δ → Prop) (l : List ε)
    (f : ε → δ → OptionT (StateT σ' ProbComp) (ForInStep δ))
    (hstep : ∀ a ∈ l, ∀ b, Inv b → ∀ st step st',
        (some step, st') ∈ support (StateT.run (f a b) st) → Inv step.value) :
    ∀ init, Inv init → ∀ st x s',
      (some x, s') ∈ support (StateT.run (forIn l init f : OptionT (StateT σ' ProbComp) δ) st) →
      Inv x := by
  induction l with
  | nil =>
    intro init hinit st x s' hx
    rw [List.forIn_nil] at hx
    simp only [show (pure init : OptionT (StateT σ' ProbComp) δ)
      = OptionT.lift (pure init) from rfl] at hx
    obtain ⟨rfl, -⟩ := hx
    exact hinit
  | cons a l ih =>
    intro init hinit st x s' hx
    rw [stateT_run_forIn_cons_mem] at hx
    obtain ⟨⟨op, sp⟩, hp, hx⟩ := hx
    have hInvStep : ∀ step, op = some step → Inv step.value := fun step hstep_eq =>
      hstep a (List.mem_cons_self) init hinit st step sp (by rw [← hstep_eq]; exact hp)
    rcases op with _ | step
    · simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hx
      obtain ⟨hxnone, -⟩ := hx
      exact absurd hxnone (by simp)
    · have hInv : Inv step.value := hInvStep step rfl
      rcases step with b | b
      · simp only [show (pure b : OptionT (StateT σ' ProbComp) δ)
          = OptionT.lift (pure b) from rfl] at hx
        obtain ⟨rfl, -⟩ := hx
        exact hInv
      · exact ih (fun a' ha' => hstep a' (List.mem_cons_of_mem _ ha')) b hInv sp x s' hx

/-! ### `simulateQ`-transport for `forIn` (OptionT (OracleComp …)) -/

variable {ι : Type} {spec : OracleSpec ι} {n : Type → Type} [Monad n] [LawfulMonad n]

/-- `simulateQ` commutes with `OptionT.pure`. -/
theorem simulateQ_optionT_pure (impl : QueryImpl spec n) (b : γ) :
    simulateQ impl (pure b : OptionT (OracleComp spec) γ) = (pure b : OptionT n γ) := by
  rw [show (pure b : OptionT (OracleComp spec) γ) = OptionT.lift (pure b)
        from (OptionT.lift_pure b).symm]
  rw [simulateQ_optionT_lift, simulateQ_pure, OptionT.lift_pure]

/-- `simulateQ` commutes with `forIn` over a list in the `OptionT (OracleComp …)` monad: simulating a
loop equals the loop whose body is the simulated body (packaged as `g` with `hg : g = simulateQ ∘ f`,
which sidesteps the elaboration ambiguity between the base- and `OptionT`-lifted `simulateQ`). This is
the structural bridge that lets the `simulateQ`-image of a loop-based `OracleVerifier.verify` body be
analyzed with the support lemmas above — it is exactly the missing `simulateQ_forIn`. -/
theorem simulateQ_optionT_forIn (impl : QueryImpl spec n)
    (l : List α) (f : α → γ → OptionT (OracleComp spec) (ForInStep γ))
    (g : α → γ → OptionT n (ForInStep γ))
    (hg : ∀ a b, g a b = simulateQ impl (f a b)) :
    ∀ init : γ,
      simulateQ impl (forIn l init f : OptionT (OracleComp spec) γ)
        = (forIn l init g : OptionT n γ) := by
  induction l with
  | nil =>
    intro init
    rw [List.forIn_nil, List.forIn_nil, simulateQ_optionT_pure]
  | cons a l ih =>
    intro init
    rw [List.forIn_cons, List.forIn_cons, simulateQ_optionT_bind, hg]
    refine bind_congr ?_
    intro step
    cases step with
    | done b => exact simulateQ_optionT_pure impl b
    | yield b => exact ih b

/-- `simulateQ` commutes with `List.Vector.mmap` in the `OptionT (OracleComp …)` monad: simulating a
vector-`mmap` of oracle queries equals the `mmap` of the simulated query body. This is the missing
`simulateQ_listVector_mmap`; it collapses the inner `(List.Vector.ofFn id).mmap` of the verifier's
fiber-query gathering loop through `simulateQ`, complementing `simulateQ_optionT_forIn`. -/
theorem simulateQ_optionT_listVector_mmap (impl : QueryImpl spec n)
    (f : α → OptionT (OracleComp spec) γ) (g : α → OptionT n γ)
    (hg : ∀ a, g a = simulateQ impl (f a)) :
    ∀ {N : ℕ} (v : List.Vector α N),
      simulateQ impl (List.Vector.mmap f v : OptionT (OracleComp spec) (List.Vector γ N))
        = (List.Vector.mmap g v : OptionT n (List.Vector γ N)) := by
  intro N v
  induction v using List.Vector.inductionOn with
  | nil =>
    rw [List.Vector.mmap_nil, List.Vector.mmap_nil, simulateQ_optionT_pure]
  | cons ih =>
    rename_i a tail
    rw [List.Vector.mmap_cons, List.Vector.mmap_cons, simulateQ_optionT_bind, hg]
    refine bind_congr ?_
    intro h'
    rw [simulateQ_optionT_bind, ih]
    refine bind_congr ?_
    intro t'
    rw [simulateQ_optionT_pure]

/-! ### `simOracle2` oracle-statement (left-family) query collapse

The query-phase `OracleVerifier.verify` body queries the *oracle statements* (via `queryCodeword`),
i.e. the LEFT family `[T₁]ₒ` of the combined spec `oSpec + ([T₁]ₒ + [T₂]ₒ)` that `toVerifier` feeds
to `simulateQ (OracleInterface.simOracle2 oSpec oStmt messages)`. The RingSwitching
`Prelude.simulateQ_simOracle2_query` only collapses a *message* (right-family) query, so it does not
apply here; we replicate the left-family analogue in-file rather than importing
`RingSwitching.Prelude` (that would make `BinaryBasefold` depend on `RingSwitching`, an inappropriate
cross-protocol import). These are protocol-agnostic and are candidates for upstreaming to
`OracleReduction/OracleInterface.lean` (which owns `simOracle2`). -/
section SimOracle2LeftQuery

open OracleInterface

variable {ι : Type} {oSpec : OracleSpec ι}
  {ι₁ : Type} {T₁ : ι₁ → Type} [∀ i, OracleInterface (T₁ i)]
  {ι₂ : Type} {T₂ : ι₂ → Type} [∀ i, OracleInterface (T₂ i)]

/-- **`simOracle2` oracle-statement-query collapse (`OracleComp` form).** Simulating, via
`simOracle2 oSpec t₁ t₂`, the lift into the combined spec `oSpec + ([T₁]ₒ + [T₂]ₒ)` of a single
query to the *left* (oracle-statement) family `[T₁]ₒ` collapses to `pure` of that oracle's `answer`,
with all queries routed to `t₁`. -/
lemma simulateQ_simOracle2_leftQuery_oc (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₁]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM (([T₁]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _)
      = (pure (OracleInterface.answer (t₁ qm.1) qm.2) : OracleComp oSpec _) := by
  change simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (liftM ((oSpec + ([T₁]ₒ + [T₂]ₒ)).query (Sum.inr (Sum.inl qm)))) = _
  rw [simulateQ_spec_query]
  -- `simOracle2` routes `inr (inl …)` to `(simOracle0 T₁ t₁).liftTarget`, i.e. `answer (t₁ …)`.
  simp only [OracleInterface.simOracle2, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply]
  change liftM (OracleInterface.simOracle0 T₁ t₁ qm) = _
  simp only [OracleInterface.simOracle0]
  rfl

/-- **`simOracle2` oracle-statement-query collapse (`OptionT`-`query` form).** The same reduction as
`simulateQ_simOracle2_leftQuery_oc`, phrased for the `query`/`monadLift` form that appears in an
`OracleVerifier.verify` body that queries an oracle statement. This is the left-family counterpart of
`RingSwitching.Prelude.simulateQ_simOracle2_query`, consumed by the query-phase verifier-run
collapse. -/
lemma simulateQ_simOracle2_leftQuery (t₁ : ∀ i, T₁ i) (t₂ : ∀ i, T₂ i)
    (qm : ([T₁]ₒ).Domain) :
    simulateQ (OracleInterface.simOracle2 oSpec t₁ t₂)
      (query (spec := [T₁]ₒ) qm : OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _)
      = (OptionT.lift (pure (OracleInterface.answer (t₁ qm.1) qm.2))
          : OptionT (OracleComp oSpec) _) := by
  rw [show (query (spec := [T₁]ₒ) qm : OptionT (OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ))) _)
        = OptionT.lift (liftM (([T₁]ₒ).query qm) : OracleComp (oSpec + ([T₁]ₒ + [T₂]ₒ)) _) from rfl]
  rw [simulateQ_optionT_lift, simulateQ_simOracle2_leftQuery_oc]
  rfl

end SimOracle2LeftQuery

end ForInSupport

/-!
## Common Proximity Check Helpers

These functions extract the shared logic between `queryOracleVerifier`
and `queryKnowledgeStateFunction` for proximity testing, allowing code reuse
and ensuring both implementations follow the same logic.
-/

/-- Extract suffix (v_{i+ϑ}, ..., v_{ℓ+R-1}) from challenge v for proximity testing -/
def extractNextSuffixFromChallenge (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (i : ℕ) (h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ) :
    (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i + ϑ, by omega⟩ := by
  let val := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate (i:=0) (k:=i + ϑ) (h_bound:=by
      simp only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add]; exact h_i_add_ϑ_le_ℓ) (x:=v)
  simp only [Fin.val_zero, zero_add] at val
  exact val

/-- This proposition declaratively captures the iterative logic of the verifier. For each repetition
and each folding step, it asserts that the folded value of the function from level `i` must equal
the value of the function from the oracle of the next level `i+ϑ`.
-/
def proximityChecksSpec (γ_challenges :
    Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (oStmt : ∀ j, OracleStatement 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ϑ (Fin.last ℓ) j)
    (fold_challenges : Fin ℓ → L) (final_constant : L) : Prop :=
  ∀ rep : Fin γ_repetitions,
    let v := γ_challenges rep
    -- For all folding levels k = 0, ..., ℓ/ϑ - 1, we track c_cur through the iterations
    ∀ k_val : Fin (ℓ / ϑ),
      let i := k_val.val * ϑ
      have h_k: k_val ≤ (ℓ/ϑ - 1) := by omega
      have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := by
        calc i + ϑ = k_val * ϑ + ϑ := by omega
          _ ≤ (ℓ/ϑ - 1) * ϑ + ϑ := by
            apply Nat.add_le_add_right; apply Nat.mul_le_mul_right; omega
          _ = ℓ/ϑ * ϑ := by
            rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel];
            conv_lhs => rw [←one_mul ϑ]
            apply Nat.mul_le_mul_right; omega
          _ ≤ ℓ := by apply Nat.div_mul_le_self;
      let k_th_oracleIdx: Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
        ⟨k_val, by simp only [toOutCodewordsCount, Fin.val_last,
          lt_self_iff_false, ↓reduceIte, add_zero, Fin.is_lt];⟩
      have h: k_th_oracleIdx.val * ϑ = i := by rw [show k_th_oracleIdx.val = k_val.val by rfl]
      have h_i_lt_ℓ: i < ℓ := by
        calc i ≤ ℓ - ϑ := by omega
          _ < ℓ := by
            apply Nat.sub_lt (by exact Nat.pos_of_neZero ℓ) (by exact Nat.pos_of_neZero ϑ)
      -- Create the suffix `(v_{i+ϑ}, ..., v_{ℓ+R-1})` as an element of `S^(i+ϑ)`
      let next_suffix_of_v := extractNextSuffixFromChallenge 𝔽q β (ϑ:=ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i h_i_add_ϑ_le_ℓ

      let next_suffix_of_v_fin : Fin (2 ^ (ℓ + 𝓡 - (i + ϑ))) :=
        by simpa [Fin.val_mk] using
          sDomainToFin 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i + ϑ, by omega⟩ (by
              apply Nat.lt_add_of_pos_right_of_le; simp only; omega) next_suffix_of_v

      -- Create the fiber evaluation mapping by querying oracle f^(i) at all fiber points
      let f_i_on_fiber : Fin (2^ϑ) → L := fun u =>
        let x: Fin (2 ^ (ℓ + 𝓡 - i)) := by
          let fiber_point_num_repr := Nat.joinBits (low := u) (high := next_suffix_of_v_fin)
          simp at fiber_point_num_repr
          have h: 2 ^ (ℓ + 𝓡 - (i + ϑ) + ϑ) = 2 ^ (ℓ + 𝓡 - i) := by
            simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
              pow_right_inj₀]
            omega
          rw [h] at fiber_point_num_repr
          exact fiber_point_num_repr
        let x_point := finToSDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by
            apply Nat.lt_add_of_pos_right_of_le; simp only; omega) x
        oStmt k_th_oracleIdx x_point

      -- Compute the next value using localized fold matrix form
      let cur_challenge_batch : Fin ϑ → L := fun j => fold_challenges ⟨i + j.val, by omega⟩

      let c_next := localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i:=⟨i, by omega⟩) (steps:=ϑ) (h_i_add_steps:=by simp only; omega)
        (r_challenges:=cur_challenge_batch) (y:=next_suffix_of_v) (fiber_eval_mapping:=f_i_on_fiber)

      -- NOTE: at i, we do the consistency check FOR THE NEXT LEVEL (`i + ϑ`):
      -- `c_next ?= f^(i + ϑ)(v_{i + ϑ}, ..., v_{ℓ+R-1})`, the final check is also covered
      let consistency_check : Prop :=
        let oracle_point_idx := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (v:=v) (i:=⟨i, by exact h_i_lt_ℓ⟩) (steps:=ϑ)
        let f_i_next_val :=
          if hk: k_val < ℓ / ϑ - 1 then
            let x_next : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i + ϑ, by omega⟩ := next_suffix_of_v
            let ⟨x_next', hx_next'⟩ := x_next
            oStmt ⟨k_val + 1, by rw [toOutCodewordsCount_last ℓ ϑ]; omega⟩
              (⟨x_next', by simpa [Nat.add_mul] using hx_next'⟩)
          else final_constant
        c_next = f_i_next_val
      consistency_check

/-- RBR knowledge error for the query phase.
Proximity testing error rate: `(1/2 + 1/(2 * 2^𝓡))^γ` -/
def queryRbrKnowledgeError := fun _ : (pSpecQuery 𝔽q β γ_repetitions
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).ChallengeIdx =>
  ((1/2 : ℝ≥0) + (1 : ℝ≥0) / (2 * 2^𝓡))^γ_repetitions

/-- Oracle query helper: query a committed codeword at a given domain point.
    Restricted to codeword indices where the oracle range is L. -/
def queryCodeword (j : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (point : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨j.val * ϑ,
      by calc
          j.val * ϑ < ℓ := by exact toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ (Fin.last ℓ) j
          _ < r := by omega⟩) :
  OracleComp ([OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
  Fin.last ℓ)]ₒ) L :=
      OracleComp.lift <| by
        simpa using
          OracleSpec.query
            (show
                [OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ.Domain from
              ⟨⟨j, by omega⟩, point⟩)

omit [CharP L 2] [SampleableType L] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero 𝓡] hdiv in
/-- **Per-query collapse for the query phase.** Simulating a single `queryCodeword`
oracle-statement query under `simOracle2 []ₒ oStmt msgs` returns `OptionT.lift (pure …)` of the
oracle statement evaluated at the query point. This holds definitionally: `queryCodeword jj point`
is `query (spec := [OracleStatement …]ₒ) ⟨⟨jj, _⟩, point⟩`, and `simOracle2`'s left-family
(oracle-statement) routing of `inr (inl …)` computes to `answer (oStmt jj) point = oStmt jj point`.
This is the load-bearing per-query primitive for collapsing the query-phase verifier run; each
`List.Vector.mmap` query body in `queryOracleVerifier.verify` reduces through it. -/
lemma queryCodeword_collapse
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (msgs : ∀ j, (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message j)
    (jj : Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)))
    (point : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨jj.val * ϑ, by
        calc jj.val * ϑ < ℓ := toCodewordsCount_mul_ϑ_lt_ℓ ℓ ϑ (Fin.last ℓ) jj
          _ < r := by omega⟩) :
    simulateQ (OracleInterface.simOracle2 ([]ₒ) oStmt msgs)
      (liftM (queryCodeword 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) jj point)
        : OptionT (OracleComp ([]ₒ
            + ([OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ)]ₒ
              + [(pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message]ₒ))) L)
      = (OptionT.lift (pure (oStmt jj point)) : OptionT (OracleComp ([]ₒ)) L) := by
  rfl

section FinalQueryRoundIOR

/-!
### IOR Implementation for the Final Query Round
-/

/-- The oracle prover for the final query phase (equivalent to regular prover). -/
noncomputable def queryOracleProver :
  OracleProver
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  PrvState := fun
    | 0 => Unit
    | 1 => Unit
  input := fun _ => ()

  sendMessage
  | ⟨0, h⟩ => nomatch h

  receiveChallenge
  | ⟨0, _⟩ => fun _ => do
    -- V sends all γ challenges v₁, ..., v_γ
    pure (fun _challenges => ())

  output := fun _ => do -- The prover always returns true since it's honest
    pure (⟨true, fun _ => ()⟩, ())

noncomputable def queryOracleVerifier :
  OracleVerifier
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  verify := fun (stmt: FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (challenges: (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Challenges) => do
    -- Get all γ challenges from the second message (final sumcheck already checked earlier).
    let c := stmt.final_constant
    let fold_challenges : Fin γ_repetitions → sDomain 𝔽q β h_ℓ_add_R_rate 0 :=
      challenges ⟨0, by rfl⟩

    -- 4. Proximity testing for all γ repetitions.
    -- This implements the specification defined in proximityChecksSpec
    for rep in (List.finRange γ_repetitions) do
      let mut c_cur : L := 0 -- Placeholder, will be initialized in the first iteration.
      let v := fold_challenges rep

      for k_val in List.finRange (ℓ / ϑ) do
        let i := k_val * ϑ
        have h_k: k_val ≤ (ℓ/ϑ - 1) := by omega
        have h_i_add_ϑ_le_ℓ : i + ϑ ≤ ℓ := by
          calc i + ϑ = k_val * ϑ + ϑ := by omega
            _ ≤ (ℓ/ϑ - 1) * ϑ + ϑ := by
              apply Nat.add_le_add_right; apply Nat.mul_le_mul_right; omega
            _ = ℓ/ϑ * ϑ := by
              rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel];
              conv_lhs => rw [←one_mul ϑ]
              apply Nat.mul_le_mul_right; omega
            _ ≤ ℓ := by apply Nat.div_mul_le_self;
        let k_th_oracleIdx: Fin (toOutCodewordsCount ℓ ϑ (Fin.last ℓ)) :=
          ⟨k_val, by simp only [toOutCodewordsCount, Fin.val_last,
            lt_self_iff_false, ↓reduceIte, add_zero, Fin.is_lt];⟩
        have h: k_th_oracleIdx.val * ϑ = i := by rw [show k_th_oracleIdx.val = k_val by rfl]
        have h_i: i = k_val * ϑ := by omega
        have h_i_lt_ℓ: i < ℓ := by
          calc i ≤ ℓ - ϑ := by omega
            _ < ℓ := by
              apply Nat.sub_lt (by exact Nat.pos_of_neZero ℓ) (by exact Nat.pos_of_neZero ϑ)
        have h_i_plus_ϑ: i + ϑ = (k_val + 1) * ϑ := by
          rw [h_i]
          conv_lhs => enter [2]; rw [←one_mul ϑ]
          rw [add_mul]

        -- Create the suffix `(v_{i+ϑ}, ..., v_{ℓ+R-1})` as an element of `S^(i+ϑ)`
        let next_suffix_of_v := extractNextSuffixFromChallenge 𝔽q β (ϑ:=ϑ)
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate) v i h_i_add_ϑ_le_ℓ

        let next_suffix_of_v_fin : Fin (2 ^ (ℓ + 𝓡 - (i + ϑ))) :=
          by simpa [Fin.val_mk] using
            sDomainToFin 𝔽q β h_ℓ_add_R_rate ⟨i + ϑ, by omega⟩ (by
                apply Nat.lt_add_of_pos_right_of_le; simp only; omega) next_suffix_of_v

        /- Create the fiber points of `next_suffix_of_v` in `S^(i)`, which have the
        form `(u_0, ..., u_{ϑ-1}, v_{i+v}, ..., v_{ℓ+R-1})`, which are actually result of the
        fiber mapping: `(q^(i+ϑ-1) ∘ ... ∘ q^(i))⁻¹({(v_{i+ϑ}, ..., v_{ℓ+R-1})})`,
        by querying the oracle `f^(i)` on all `2^ϑ` fiber points using queryCodeword helper.

        DESIGN NOTE (length-carrying restructure): the fiber evaluations are gathered into a
        `List.Vector L (2^ϑ)` via `List.Vector.mmap` rather than into a plain `List L` via
        `List.mapM`. The previous list-based form forced a downstream obligation
        `f_i_on_fiber.length = 2 ^ ϑ` to justify the `Fin (2^ϑ)`-indexed accesses below; but
        under the monadic bind `f_i_on_fiber` is a lambda-bound free variable, so that length
        equation would have to hold for ALL lists of the binder's type and is therefore
        unprovable (and this toolchain has neither a `List.length_mapM` lemma nor VCVio's
        `mem_support_vector_mapM` helper). Carrying the length in the type via
        `List.Vector` makes the obligation vanish: `List.Vector.get : Fin (2^ϑ) → L` is total,
        so both consumers below index without any side proof. Semantics are unchanged — the same
        `2^ϑ` oracle queries are issued, in the same order (`(List.Vector.ofFn id).mmap` visits
        `u = 0, 1, ..., 2^ϑ-1`), with the same per-index query body, and `(ofFn id).get u = u`. -/
        let f_i_on_fiber : List.Vector L (2^ϑ) ←
          (List.Vector.ofFn (n := 2^ϑ) (id : Fin (2^ϑ) → Fin (2^ϑ))).mmap (fun (u : Fin (2^ϑ)) => do
          let x: Fin (2 ^ (ℓ + 𝓡 - i)) := by
            let fiber_point_num_repr := Nat.joinBits (low := u) (high := next_suffix_of_v_fin)
            simp at fiber_point_num_repr
            have h: 2 ^ (ℓ + 𝓡 - (i + ϑ) + ϑ) = 2 ^ (ℓ + 𝓡 - i) := by
              simp only [Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one, not_false_eq_true,
                pow_right_inj₀]
              omega
            rw [h] at fiber_point_num_repr
            exact fiber_point_num_repr
          let x_point := finToSDomain 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ (by
              apply Nat.lt_add_of_pos_right_of_le; simp only; omega) x
          queryCodeword 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (j := k_th_oracleIdx) (point := x_point)
        )

        if i > 0 then
          -- cᵢ ?= f^(i)(vᵢ, ..., v_{ℓ+R-1})
          let oracle_point_idx := extractMiddleFinMask 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (v:=v) (i:=⟨i, by exact h_i_lt_ℓ⟩) (steps:=ϑ)

          let f_i_val := f_i_on_fiber.get oracle_point_idx
          unless c_cur = f_i_val do
            return false

        let cur_challenge_batch : Fin ϑ → L := fun j => stmt.challenges ⟨i +
        j.val, by rw [Fin.val_last]; omega⟩

        let c_next := localized_fold_matrix_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i:=⟨i, by omega⟩) (steps:=ϑ) (h_i_add_steps:=by simp only; omega)
          (r_challenges:=cur_challenge_batch) (y:=next_suffix_of_v)
          (fiber_eval_mapping:=f_i_on_fiber.get)

        -- Update c_prev_iter for the next loop iteration's check.
        c_cur := c_next

      -- Final check after all folding: `c_ℓ ?= c`.
      unless c_cur = c do
        return false

  -- If all repetitions and all checks pass, the verifier accepts.
    return true
  embed := ⟨Empty.elim, fun a b => Empty.elim a⟩
  hEq := fun i => Empty.elim i

/-- The oracle reduction for the final query phase. -/
noncomputable def queryOracleReduction :
  OracleReduction
    (oSpec := []ₒ)
    (StmtIn := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStmtIn := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (WitIn := Unit)
    (StmtOut := Bool)
    (OStmtOut := fun _ : Empty => Unit)
    (WitOut := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  prover := queryOracleProver 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  verifier := queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- The final query round as an `OracleProof` (since it outputs Bool and no oracle statements). -/
noncomputable def queryOracleProof : OracleProof
    (oSpec := []ₒ)
    (Statement := FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
    (OStatement := OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (
    Fin.last ℓ))
    (Witness := Unit)
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) :=
  queryOracleReduction 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)

/-- Perfect completeness for the final query round (using the oracle queryProof). -/
theorem queryOracleProof_perfectCompleteness {σ : Type}
  (init : ProbComp σ)
  (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  OracleProof.perfectCompleteness
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relation := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (oracleProof := queryOracleProof 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (init := init)
    (impl := impl) := by
  unfold OracleProof.perfectCompleteness
  intro stmtIn witIn h_relIn
  -- RESIDUAL (protocol-specific honest-acceptance, NOT a missing primitive). Perfect completeness
  -- asks for `Pr[honest run accepts] = 1`. The forIn-with-early-exit support/transport theory that
  -- this once needed NOW EXISTS in the `ForInSupport` section above: `simulateQ_optionT_forIn`
  -- pushes `simulateQ` through the doubly-nested `forIn`, `simulateQ_optionT_listVector_mmap`
  -- collapses the inner `2^ϑ`-query `List.Vector.mmap`, and `forIn_yield_pure_eq_foldl` collapses an
  -- all-pass (all-`yield`) loop to a deterministic `pure` of a fold. What remains is genuinely
  -- protocol-specific and research-tier: one must prove the HONEST RUN's per-iteration checks all
  -- pass — i.e. `c_cur = f^(i)(v_i,…)` at every fold level and `c_cur = c` at the end — from
  -- `finalSumcheckRelOut` (= `finalNonDoomedFoldingProp`). That is the BaseFold fold/oracle
  -- correctness argument (`localized_fold_matrix_form` equals the next-level codeword value on the
  -- honest oracles), not loop plumbing; only once it is in hand does `forIn_yield_pure_eq_foldl`
  -- finish the `= 1` via the no-early-exit collapse. Out of scope for this file's loop-theory remit.
  sorry

open scoped NNReal

/-- The round-by-round extractor for the query phase.
Since f^(0) is always available, we can invoke the extractMLP function directly. -/
noncomputable def queryRbrExtractor :
  Extractor.RoundByRound []ₒ
    (StmtIn := (FinalSumcheckStatementOut (L:=L) (ℓ:=ℓ))
      × (∀ j, OracleStatement 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j))
    (WitIn := Unit)
    Unit
    (pSpec := pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (fun _ => Unit) where
  eqIn := rfl
  extractMid := fun _ _ _ witMidSucc => witMidSucc
  extractOut := fun _ _ _ => ()

def queryKStateProp {m : Fin (1 + 1)}
  (tr : ProtocolSpec.Transcript m
    (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)))
  (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ))
  (witMid : Unit)
  (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j) : Prop :=
if h0 : m.val = 0 then
  -- Same as last Kstate of finalSumcheck reduction
  Binius.BinaryBasefold.finalSumcheckRelOutProp 𝔽q β (input:=⟨⟨stmt, oStmt⟩, witMid⟩)
else
    let r := stmt.ctx.t_eval_point
    let s := stmt.ctx.original_claim
    let challenges : Fin ℓ → L := stmt.challenges
    let tr_so_far := (pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).take m m.is_le
    let chalIdx : tr_so_far.ChallengeIdx := ⟨⟨0,
      Nat.lt_of_succ_le (by omega)⟩, by simp only [Nat.reduceAdd]; rfl⟩
    let γ_challenges : Fin γ_repetitions → sDomain 𝔽q
      β h_ℓ_add_R_rate ⟨0, by omega⟩ := ((ProtocolSpec.Transcript.equivMessagesChallenges (k:=m)
        (pSpec:=pSpecQuery 𝔽q β γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
        tr).2 chalIdx)
    let fold_challenges := stmt.challenges
    -- Checks available after message 1 (V -> P: γ challenges)
    let proximityTestsCheck : Prop :=
      proximityChecksSpec 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (ϑ:=ϑ) γ_repetitions γ_challenges oStmt fold_challenges stmt.final_constant
    proximityTestsCheck

/-- The knowledge state function for the query phase -/
noncomputable def queryKnowledgeStateFunction {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
  (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).KnowledgeStateFunction init impl
  (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
  (relOut := acceptRejectOracleRel)
  (extractor := queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) where
  toFun := fun m ⟨stmt, oStmt⟩ tr witMid =>
    queryKStateProp 𝔽q β (ϑ:=ϑ) (γ_repetitions:=γ_repetitions)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (m:=m) (tr:=tr) (stmt:=stmt) (witMid:=witMid) (oStmt:=oStmt)
  toFun_empty := fun stmt witMid => by simp only; rfl
  toFun_next := fun m hDir stmt tr msg witMid h => by
    fin_cases m; simp [pSpecQuery] at hDir
  toFun_full := fun stmt tr witOut h => by
    -- Mechanical reduction (verified to reach the wedge below): unfold the positive-probability
    -- hypothesis to a membership in the support of the simulated verifier run.
    rw [gt_iff_lt, probEvent_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    rw [OptionT.mem_support_iff] at hx
    simp only [OptionT.run_mk, support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    simp only [OracleVerifier.toVerifier, Verifier.run, StateT.run'_eq,
      support_map, Set.mem_image, Prod.exists] at hx
    obtain ⟨a, b, hx, hab⟩ := hx
    -- Expose the loop structure: `simp [queryOracleVerifier, simulateQ_optionT_bind]` rewrites the
    -- `simulateQ (simOracle2 …) (verify …)` into the explicit DOUBLY-NESTED `forIn` over
    -- `MProd (Option Bool) _` accumulators (the `do`-notation early-return desugaring), with the inner
    -- `(List.Vector.ofFn id).mmap` of `2^ϑ` oracle queries and the `unless … do return false` exits
    -- rendered as `ForInStep.yield ⟨none, …⟩` / `ForInStep.done ⟨some false, …⟩`.
    simp only [queryOracleVerifier, simulateQ_optionT_bind] at hx
    -- GOAL REDUCTION (verified to land): the accept witness `hrel` collapses to `x = (true, _)`, the
    -- last-round extractor is the identity on `()`, and `queryKStateProp` at `m = .last 1` (value `1`,
    -- so the `m.val = 0` `dite` is false) is exactly `proximityChecksSpec` on the round-1 challenges.
    obtain ⟨stmt1, oStmt⟩ := stmt
    rw [acceptRejectOracleRel] at hrel
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hrel
    obtain ⟨hx_eq, -⟩ := hrel
    simp only [queryRbrExtractor]
    unfold queryKStateProp
    simp only [Fin.val_last, one_ne_zero, ↓reduceDIte]
    -- ⊢ proximityChecksSpec 𝔽q β γ_repetitions
    --     ((Transcript.equivMessagesChallenges tr).2 ⟨⟨0,_⟩,_⟩) oStmt
    --     stmt1.challenges stmt1.final_constant
    --
    -- VERIFIED VERIFIER-RUN QUERY COLLAPSE (this whole `simp only` block compiles): push both
    -- `simulateQ` layers through the doubly-nested `forIn` and the inner `2^ϑ`-query
    -- `List.Vector.mmap`, collapsing EVERY oracle-statement query to `pure (oStmt …)` via the
    -- in-file `queryCodeword_collapse` (a `rfl`). After this, `hx` is membership in the support of a
    -- fully QUERY-FREE doubly-nested `forIn` over `StateT σ ProbComp`'s `OptionT` (no `unifSpec`
    -- sampling, no `[]ₒ`/oracle-statement queries remain inside the loop bodies).
    simp only [ForInSupport.simulateQ_optionT_forIn,
      ForInSupport.simulateQ_optionT_listVector_mmap,
      simulateQ_optionT_bind, ForInSupport.simulateQ_optionT_pure,
      queryCodeword_collapse, simulateQ_optionT_lift, simulateQ_pure,
      apply_ite, bind_pure_comp, map_pure, pure_bind] at hx
    -- SHARPENED RESIDUAL (query plumbing DONE; what remains is transformer-stack support + the
    -- no-early-exit invariant + the BaseFold cast alignment — NOT any missing query/loop primitive).
    -- After the collapse above, `hx` reads (schematically):
    --   (a, b) ∈ support (StateT.run ((·, oStmtOut) <$>
    --     (do let r ← forIn (finRange γ) ⟨none,()⟩ (fun rep acc =>
    --            do let r' ← forIn (finRange (ℓ/ϑ)) ⟨none,0⟩ (fun k c =>
    --                 do let fib ← (ofFn id).mmap (fun u => OptionT.lift (pure (oStmt ⟨k,_⟩ …)));
    --                    if k*ϑ>0 then (if c.snd = fib.get (extractMiddleFinMask …)
    --                                   then pure (.yield ⟨none, localized_fold_matrix_form … fib.get⟩)
    --                                   else pure (.done ⟨some false, c.snd⟩))
    --                    else pure (.yield ⟨none, localized_fold_matrix_form … fib.get⟩));
    --               simulateQ impl (simulateQ (simOracle2 …)
    --                 (match r'.fst with | none => if r'.snd = final_constant then .yield ⟨none,()⟩
    --                                              else .done ⟨some false,()⟩
    --                                   | some a => .done ⟨some a,()⟩)));
    --         simulateQ impl (simulateQ (simOracle2 …)
    --           (match r.fst with | none => pure true | some a => pure a))) s)
    -- VERIFIED ADVANCE (landed): peel the outer `OptionT (StateT σ ProbComp)` functor map to an
    -- `OptionT` bind, exposing `hx` as membership in the support of the `StateT.run … s`-evaluation of
    -- `outerLoop >>= finalContinuation`. (`StateT.run_map` does NOT fire here: the map is the OptionT
    -- functor map, not a `StateT`-level map — confirmed by `pp.explicit`.)
    rw [show (∀ {X Y} (f : X → Y) (x : OptionT (StateT σ ProbComp) X),
          f <$> x = x >>= (pure ∘ f)) from fun f x => map_eq_pure_bind f x] at hx
    -- SHARPENED RESIDUAL (corrected: the prior note claimed the loop-support machinery for steps 1-2
    -- was "in hand"; it was NOT — `ForInSupport.forIn_support_invariant` needs `[HasEvalSet m]` for the
    -- loop monad, but `HasEvalSet (StateT σ ProbComp)` does NOT exist, so it does not apply to this
    -- `OptionT (StateT σ ProbComp)` loop as-is. The genuinely missing primitive — a
    -- `StateT.run`-evaluated `forIn` support transport, landing the loop at the `ProbComp` level where
    -- `support` IS defined — is now PROVEN above: `ForInSupport.stateT_run_forIn_cons_mem` (cons-step
    -- membership via `List.forIn_cons` + the monad-instance unfolds + `mem_support_bind_iff`) and
    -- `ForInSupport.stateT_run_forIn_support_invariant` (the induction-free `Inv`-rule, the
    -- `OptionT (StateT σ ProbComp)` analogue of `forIn_support_invariant`). The remaining work, now
    -- resting on a REAL primitive rather than a missing one:
    --  (1) OUTER NO-EARLY-EXIT. Split `hx` at the outer `>>= finalContinuation` (one `StateT.run`/
    --      `OptionT`-bind step), exposing the outer-loop result `r : MProd (Option Bool) PUnit` in
    --      `support (StateT.run outerLoop s')`. Apply `stateT_run_forIn_support_invariant` with
    --      `Inv acc := acc.fst = none`; the per-rep step obligation (the inner `match acc.fst`
    --      continuation only ever writes `done ⟨some false,_⟩` on a FAILED check and `yield ⟨none,_⟩`
    --      otherwise) discharges by `cases acc.fst` (which ι-reduces the content-addressed verifier
    --      matcher `queryOracleVerifier.match_1`, after which each branch is a `pure` collapsed by
    --      `simulateQ_optionT_pure`). With `hab/hx_eq` forcing `r = some (true,_)`, conclude
    --      `r.fst = none`, so every per-rep `unless` and the final `unless c_cur = c` held.
    --  (2) PER-REP INNER INVARIANT. Same `stateT_run_forIn_support_invariant` on the inner
    --      `forIn (finRange (ℓ/ϑ))` loop, `Inv c := c.fst = none`, transports each fold-level
    --      consistency check `c_cur = f^(i)(v_i,…)` out of the inner support.
    --  (3) CAST ALIGNMENT (the heavy, BaseFold-specific remainder, unchanged). Match the loop's
    --      `f_i_on_fiber`/`c_cur`/`c_next` (`localized_fold_matrix_form`, `extractMiddleFinMask`,
    --      `next_suffix_of_v`, with their `Fin`/`Nat.joinBits` casts) against the identically-shaped
    --      `proximityChecksSpec` terms, reconciling the ONE-ITERATION SHIFT (verifier checks level `i`
    --      at the START of iteration `i+ϑ`). Lemma 4.9 `iterated_fold_eq_matrix_form` +
    --      `localized_fold_eval_succ`/`_zero` + `foldMatrixNat_succ_apply` (proven in Prelude) supply
    --      the fold-semantics facts. This index/cast bookkeeping is the genuine remaining content.
    have peel : ∀ {W Y : Type} (mx : OptionT (StateT σ ProbComp) W)
        (g : W → OptionT (StateT σ ProbComp) Y) (st : σ)
        (z : Option Y × σ),
        z ∈ support (StateT.run (mx >>= g : OptionT (StateT σ ProbComp) Y) st) ↔
          ∃ p ∈ support (StateT.run mx st),
            z ∈ support
              (match p.1 with
                | some bv => StateT.run (g bv) p.2
                | none => (pure (none, p.2) : ProbComp (Option Y × σ))) := by
      intro W Y mx g st z
      simp only [bind, OptionT.bind, OptionT.mk, StateT.bind, StateT.run]
      erw [mem_support_bind_iff]
      apply exists_congr; intro p
      apply and_congr_right; intro _
      rcases p with ⟨op, sp⟩
      rcases op with _ | bv <;> rfl
    have peel_map : ∀ {X Y : Type} (mx : OptionT (StateT σ ProbComp) X)
        (K : X → Y) (st : σ) (z : Option Y × σ),
        z ∈ support (StateT.run (mx >>= (pure ∘ K) : OptionT (StateT σ ProbComp) Y) st) ↔
          ∃ p ∈ support (StateT.run mx st), z = (Option.map K p.1, p.2) := by
      intro X Y mx K st z
      simp only [bind, OptionT.bind, OptionT.mk, StateT.bind, StateT.run, Function.comp_apply]
      erw [mem_support_bind_iff]
      apply exists_congr; intro p
      apply and_congr_right; intro _
      obtain ⟨op, sp⟩ := p
      cases op with
      | none =>
        show z ∈ _root_.support (pure ((none, sp) : Option Y × σ)) ↔ _
        simp only [support_pure, Set.mem_singleton_iff, Option.map_none]
      | some bv =>
        show z ∈ _root_.support (pure ((some (K bv), sp) : Option Y × σ)) ↔ _
        simp only [support_pure, Set.mem_singleton_iff, Option.map_some]
    have runpure : ∀ {X : Type} (w : X) (st : σ) (z : Option X × σ),
        z ∈ support (StateT.run (pure w : OptionT (StateT σ ProbComp) X) st) ↔
          z = (some w, st) := by
      intro X w st z
      show z ∈ _root_.support (pure ((some w, st) : Option X × σ)) ↔ _
      simp only [support_pure, Set.mem_singleton_iff]
    rw [peel_map] at hx
    obtain ⟨p, hp, hx⟩ := hx
    subst hx_eq
    rw [hab] at hx
    have hp_true : p.1 = some true := by
      have h1 := congrArg (fun w => Option.map Prod.fst w.1) hx
      simp only [Option.map_map, Function.comp_def, Option.map_some, Option.map_id_fun',
        id_eq] at h1
      exact h1.symm
    rw [peel] at hp
    obtain ⟨q, hq, hp⟩ := hp
    obtain ⟨q1, q2⟩ := q
    -- Apply the outer invariant to hq IN PLACE (body unifies from hq's type).
    rcases hq1 : q1 with _ | rv
    · simp only [hq1, support_pure, Set.mem_singleton_iff] at hp
      rw [hp] at hp_true; simp at hp_true
    · have hrv_ne : rv.fst ≠ some true := by
        revert hq
        rw [hq1]
        intro hq
        refine ForInSupport.stateT_run_forIn_support_invariant
          (fun acc => acc.fst ≠ some true) _ _ ?step _ (by simp) _ _ _ hq
        intro rep _ b hb st step st' hstepmem
        -- OUTER step obligation: peel the inner loop + post-inner matcher, get step.value.
        rw [peel] at hstepmem
        obtain ⟨ai, hai, hstepmem⟩ := hstepmem
        obtain ⟨ai1, ai2⟩ := ai
        -- Post-inner matcher: `step` is determined by `ai1` (the inner OptionT result).
        rcases hai1 : ai1 with _ | ic
        · -- inner produced `none` ⟹ post-inner tail is `pure (none, ai2)`
          simp only [hai1, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hstepmem
          exact absurd hstepmem.1 (by simp)
        · -- inner produced `some ic`; get the inner early-exit flag fact.
          have hic : ic.fst ≠ some true := by
            revert hai
            rw [hai1]
            intro hai
            refine ForInSupport.stateT_run_forIn_support_invariant
              (fun acc : MProd (Option Bool) L => acc.fst ≠ some true)
              _ _ ?innerstep _ (by simp) _ _ _ hai
            intro k _ c hc st2 stp st2' hmem2
            rw [peel] at hmem2
            obtain ⟨fibp, hfib, hmem2⟩ := hmem2
            obtain ⟨fib1, fib2⟩ := fibp
            rcases hfib1 : fib1 with _ | fib
            · simp only [hfib1, support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hmem2
              exact absurd hmem2.1 (by simp)
            · simp only [hfib1] at hmem2
              split at hmem2
              · split at hmem2
                · rw [runpure, Prod.mk.injEq, Option.some.injEq] at hmem2
                  obtain ⟨hstp, -⟩ := hmem2; subst hstp; simp
                · rw [runpure, Prod.mk.injEq, Option.some.injEq] at hmem2
                  obtain ⟨hstp, -⟩ := hmem2; subst hstp; simp
              · rw [runpure, Prod.mk.injEq, Option.some.injEq] at hmem2
                obtain ⟨hstp, -⟩ := hmem2; subst hstp; simp

          rw [hai1] at hstepmem
          obtain ⟨ic1, ic2⟩ := ic
          rcases hicf : ic1 with _ | a
          · simp only [hicf] at hstepmem
            split at hstepmem
            · simp only [ForInSupport.simulateQ_optionT_pure, runpure, Prod.mk.injEq,
                Option.some.injEq] at hstepmem
              obtain ⟨hs, -⟩ := hstepmem; subst hs; simp
            · simp only [ForInSupport.simulateQ_optionT_pure, runpure, Prod.mk.injEq,
                Option.some.injEq] at hstepmem
              obtain ⟨hs, -⟩ := hstepmem; subst hs; simp
          · simp only [hicf, ForInSupport.simulateQ_optionT_pure, runpure, Prod.mk.injEq,
              Option.some.injEq] at hstepmem
            obtain ⟨hs, -⟩ := hstepmem; subst hs
            simp only [ForInStep.value]
            intro hcontra
            rw [hicf] at hic
            exact hic hcontra

      -- With `hrv_ne` in hand: collapse the post-loop matcher and close the false-accept arm.
      simp only [hq1] at hp
      rcases hrv : rv.fst with _ | c
      · -- ACCEPT PATH: `rv.fst = none`. The outer loop completed all γ reps with NO early
        -- `done` exit, so EVERY per-rep `unless c_cur = …` and the final `unless c_cur = c`
        -- held. `hp : p ∈ support (StateT.run (pure true) q2)` (consistent with `hp_true`).
        simp only [hrv, ForInSupport.simulateQ_optionT_pure, runpure] at hp
        -- ════════════════════════════════════════════════════════════════════════════
        -- SHARPENED RESIDUAL — the genuine remaining content: BaseFold cast alignment.
        -- Steps 1–3 are DONE: the verifier run is peeled to the outer-loop result, the
        -- accept Bool pins it to `some true`, the content-addressed matcher has FALLEN
        -- (via `simulateQ_optionT_pure`), and BOTH the outer and inner `forIn` invariants
        -- (`stateT_run_forIn_support_invariant`, `Inv acc := acc.fst ≠ some true`) are
        -- applied & discharged, establishing `rv.fst = none` (no early exit) — i.e. every
        -- per-(rep, fold-level) consistency check passed.
        --
        -- What remains is to convert "no early `done` exit" into `proximityChecksSpec`:
        -- re-enter the inner `forIn (finRange (ℓ/ϑ))` per rep with the SAME inner invariant
        -- specialized to surface, at each level `k`, the passed check `c_cur = f^(k·ϑ)(…)`,
        -- then RECONCILE the loop's `localized_fold_matrix_form` / `extractMiddleFinMask` /
        -- `extractNextSuffixFromChallenge` terms (with their `Fin` / `Nat.joinBits` casts
        -- and the ONE-ITERATION SHIFT: the verifier checks level `i` at the START of
        -- iteration `i+ϑ`) against the identically-shaped `proximityChecksSpec`
        -- `consistency_check`. Lemma 4.9 `iterated_fold_eq_matrix_form` +
        -- `localized_fold_eval_succ`/`_zero` + `foldMatrixNat_succ_apply` (all proven in
        -- Prelude) supply the fold semantics; this index/cast bookkeeping is the genuine
        -- remaining BaseFold-specific content. The loop body itself cannot be restated by
        -- hand — `simulateQ (simOracle2 …)`'s message-family `OracleInterface` is not
        -- synthesizable out of context (the elaboration ambiguity the in-file
        -- `simulateQ_optionT_*` lemmas sidestep) — so this final extraction must thread the
        -- inner invariant through `hq`'s body IN PLACE, as the invariant applications above
        -- already do.
        sorry
      · -- FALSE-ACCEPT PATH ruled out: `rv.fst = some c` forces (via `hp` + `hp_true`)
        -- `c = true`, i.e. `rv.fst = some true`, contradicting the outer invariant `hrv_ne`.
        exfalso
        simp only [hrv, ForInSupport.simulateQ_optionT_pure, runpure] at hp
        rw [hp] at hp_true
        simp only [Option.some.injEq] at hp_true
        exact hrv_ne (by rw [hrv, hp_true])



/-- Round-by-round knowledge soundness for the oracle verifier (query phase) -/
theorem queryOracleVerifier_rbrKnowledgeSoundness [Fintype L] {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (queryOracleVerifier 𝔽q β (ϑ:=ϑ) γ_repetitions).rbrKnowledgeSoundness init impl
    (relIn := finalSumcheckRelOut 𝔽q β (ϑ:=ϑ) (h_ℓ_add_R_rate := h_ℓ_add_R_rate))
    (relOut := acceptRejectOracleRel)
    (rbrKnowledgeError := queryRbrKnowledgeError 𝔽q β γ_repetitions
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)) := by
  use fun _ => Unit
  use queryRbrExtractor 𝔽q β (ϑ:=ϑ) γ_repetitions (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
  use queryKnowledgeStateFunction 𝔽q β (ϑ:=ϑ) γ_repetitions init impl
  intro stmtIn witIn prover j
  -- RESIDUAL (research-tier; the loop-support primitive is no longer the blocker). The dominant
  -- obstruction is intrinsic: the target error `(1/2 + 2^-(𝓡+1))^γ` is the proximity-gap bound, whose
  -- proof needs the Binius/BaseFold list-decoding proximity argument (per-repetition soundness
  -- `1/2 + 2^-(𝓡+1)`, independence across the `γ` repetitions) — genuine research-tier content not
  -- yet formalized in this development. The structural step (bounding the probability the
  -- `forIn`-loop verifier accepts a state failing `queryKStateProp`) now HAS its loop-support
  -- machinery available — the `ForInSupport` section above supplies both the `simulateQ`-transport
  -- (`simulateQ_optionT_forIn`, `simulateQ_optionT_listVector_mmap`) AND the
  -- `StateT.run`-evaluated loop-support transport (`stateT_run_forIn_cons_mem`,
  -- `stateT_run_forIn_support_invariant`) that `forIn_support_invariant` could NOT provide for this
  -- `OptionT (StateT σ ProbComp)` loop (no `HasEvalSet (StateT σ ProbComp)`) — but it bottoms out in
  -- the same proximity bound. Not closable in this single file under the honest-proof constraints
  -- (no axioms, no weakening of the bound, no assume-the-conclusion).
  sorry

end FinalQueryRoundIOR
end
end Binius.BinaryBasefold.QueryPhase

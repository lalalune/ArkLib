/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma512Honest
import VCVio.OracleComp.QueryTracking.Birthday

/-!
# Birthday-bound bricks for the DSFS bad events (CO25 Lemma 5.8 / Claim 5.21, R1)

This module lands the **R1** layer of the bricks decomposition for the DSFS Key Lemma
(CO25, Lemma 5.1): generic, unconditionally-proven probability bricks for adaptive query
games answered by fresh uniform draws, the numeric bridges onto the in-tree §5.8 claim
bounds, and the honest-bad-event domination that channels the M2 residuals of
`KeyLemmaFoundations` into a single trace-level event `E`.

VCVio already proves the ROM birthday bound for *input-distinct output collisions* of a
`loggingOracle` trace (`OracleComp.probEvent_logCollision_le_birthday_total`,
`OracleComp.probEvent_cacheCollision_le_birthday_total_tight`). The bricks here are the
complementary shapes that the CO25 §5.6 analysis needs and VCVio lacks:

- a reusable **master accumulator lemma** (`probEvent_simulateQ_stateT_le_sum_of_step`):
  per-step bad-event costs of a stateful `QueryImpl` sum across an adaptively chosen
  `T`-query computation;
- **answer collisions** under fresh uniform draws — the new answer collides with *any*
  earlier answer, no input-distinctness side condition — at `T(T−1)/(2|X|) ≤ T²/(2|X|)`;
- **adversarial-set landing** — some answer lands in a query-dependent (hence adaptively
  chosen) set of size ≤ `k` — at `Tk/|X|`.

## Proven (no `sorry`, axiom-clean)

- `probEvent_simulateQ_stateT_le_sum_of_step` (R1a): if every handler step, run from a
  non-bad state of size `m`, turns the state bad with probability ≤ `ε m` and grows the
  size by at most one, then a `T`-query computation started at a non-bad `s₀` ends bad with
  probability ≤ `∑_{i<T} ε (size s₀ + i)`.
- `probEvent_collision_freshUniformLog_le_tight` / `probEvent_collision_freshUniformLog_le`
  (R1b): `T` adaptive queries answered by fresh uniform draws over a finite `X` produce two
  equal answers with probability ≤ `T(T−1)/(2|X|) ≤ T²/(2|X|)` (the CO25 Lemma 5.8 /
  birthday shape).
- `probEvent_hit_freshUniformHit_le` (R1c): some fresh uniform answer lands in the
  adversarially-chosen (query-indexed) target set of size ≤ `k` with probability ≤ `Tk/|X|`
  (the CO25 Lemma 5.8 "hit a prior capacity segment" shape).
- `lemma5_8Bound_eq_claim5_21Bound` (R1d): the Lemma 5.8 bound family `(7T²−3T)/(2|Σ|^c)`
  evaluated at the Hyb₀/Hyb₁ trace length `tₕ+1+tₚ+L+tₚᵢ` *is* the in-tree
  `claim5_21Bound` (definitionally).
- `birthday_toReal_le_lemma5_8Bound` / `hit_toReal_le_capacityRatio` (R1d): the ENNReal
  outputs of the generic bricks, over any answer space at least as large as the capacity
  space `|U|^C`, are dominated by the real-valued CO25 bounds.
- `probEvent_honestBad_le_probEvent_E` (R1e): **modulo the M2 statement interfaces**
  (`Lemma5_12HonestResidual`, the refuted legacy `Lemma5_14HonestFalseStatement`, and
  `Lemma5_16HonestResidual`), the honest CO25 bad events
  `E_inv/E_fork/E_time` over `Backtrack.S_BT` are dominated — for *any* trace
  distribution — by the single trace event `E` (CO25 §5.6), reducing their probability
  bound to Lemma 5.8.
- `honestBad_birthday_of_residuals` (R1 assembly): M2 + the legacy
  `Lemma5_8EagerBirthdayFalseStatement` imply the honest bad events of the eager
  `D_𝔖`-carrier game are bounded by `lemma5_8Bound` (= `claim5_21Bound` at the game's
  trace length).

## Legacy false statement, not a live residual

- `Lemma5_8EagerBirthdayFalseStatement`: the original in-tree attempt at CO25 Lemma 5.8 over
  the eager `D_DS` carrier. It is kept only as a refuted historical surface with a
  machine-checked countermodel; use `BirthdayBoundPaper.Lemma5_8EagerPaperResidual` for the
  repaired paper-faithful obligation.

## Claim-numbering note

The scoping prompt for this lane labels the Hyb₁→Hyb₂ bad-event bound "birthday-type
Claim 5.22". In the in-tree numerics (`KeyLemmaFoundations`), the **birthday** bound is
`claim5_21Bound` (Lemma 5.8 at the Hyb₀/Hyb₁ trace length, consumed by `Hyb01StepResidual`),
while `claim5_22Bound` is the codec-decoding-bias bound of Eq. 53 (consumed by
`Hyb12StepResidual`). This module therefore targets `claim5_21Bound`; nothing
birthday-shaped is owed to `claim5_22Bound`.
-/

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.BirthdayBound

open KeyLemmaFoundations
open scoped NNReal ENNReal

/-! ## R1a — master accumulator: per-step bad-event costs sum across an adaptive run

The CO25 §5.6 events become bad exactly once, at the step where a fresh draw collides with
(or lands in) data accumulated so far; the per-step cost grows with the amount of
accumulated data. This is the generic carrier: a state-monad implementation whose step,
from a non-bad state of size `m`, goes bad with probability ≤ `ε m` and grows the size by
at most one. No absorbing/monotonicity assumption on `bad` is needed — the bad branch of
each step is paid in full (`≤ 1`) by the union bound. -/

/-- R1a — **master accumulator lemma**. Let `impl` answer queries inside `StateT σ ProbComp`
and let `bad : σ → Prop` be an event on states with a size measure `size : σ → ℕ`. If

* from every non-bad state `s`, one handler step goes bad with probability at most
  `ε (size s)` (`hstep_bad`), and grows the size by at most one (`hstep_size`), and
* `ε` is monotone,

then any computation making at most `T` queries (`IsTotalQueryBound`), started at a non-bad
state `s₀`, ends in a bad state with probability at most `∑_{i<T} ε (size s₀ + i)`.
This is the union-bound skeleton of CO25 Lemma 5.8 (and of the textbook birthday argument);
VCVio proves the special case hard-wired to `cachingOracle` inside
`probEvent_cacheCollision_le_birthday_total_tight`. -/
theorem probEvent_simulateQ_stateT_le_sum_of_step
    {ι : Type} {spec : OracleSpec ι} {α σ : Type}
    {impl : QueryImpl spec (StateT σ ProbComp)}
    {bad : σ → Prop} {size : σ → ℕ} {ε : ℕ → ℝ≥0∞} (hmono : Monotone ε)
    (hstep_bad : ∀ (t : spec.Domain) (s : σ), ¬ bad s →
      Pr[ fun us : spec.Range t × σ => bad us.2 | (impl t).run s] ≤ ε (size s))
    (hstep_size : ∀ (t : spec.Domain) (s : σ), ¬ bad s →
      ∀ us ∈ support ((impl t).run s), size us.2 ≤ size s + 1)
    {oa : OracleComp spec α} (T : ℕ) (hT : IsTotalQueryBound oa T)
    (s₀ : σ) (h₀ : ¬ bad s₀) :
    Pr[ fun xs : α × σ => bad xs.2 | (simulateQ impl oa).run s₀] ≤
      ∑ i ∈ Finset.range T, ε (size s₀ + i) := by
  induction oa using OracleComp.inductionOn generalizing T s₀ with
  | pure x =>
      simp only [simulateQ_pure, StateT.run_pure]
      refine le_trans (le_of_eq (probEvent_eq_zero fun z hz hbad => ?_)) (zero_le _)
      rw [support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact h₀ hbad
  | query_bind t mx ih =>
      rw [isTotalQueryBound_query_bind_iff] at hT
      obtain ⟨hTpos, hrest⟩ := hT
      rw [simulateQ_query_bind, StateT.run_bind]
      simp only [OracleQuery.input_query, monadLift_self]
      have hmain := probEvent_bind_le_add
        (mx := (impl t).run s₀)
        (my := fun us => (simulateQ impl (mx us.1)).run us.2)
        (p := fun us : spec.Range t × σ => ¬ bad us.2)
        (q := fun xs : α × σ => ¬ bad xs.2)
        (ε₁ := ε (size s₀))
        (ε₂ := ∑ i ∈ Finset.range (T - 1), ε (size s₀ + 1 + i))
        (by simpa [not_not] using hstep_bad t s₀ h₀)
        (fun us hus hnb => by
          refine le_trans (by simpa [not_not] using ih us.1 (T - 1) (hrest us.1) us.2 hnb) ?_
          refine Finset.sum_le_sum fun i _ => hmono ?_
          have := hstep_size t s₀ h₀ us hus
          omega)
      refine le_trans (by simpa [not_not] using hmain) ?_
      have hT1 : T = (T - 1) + 1 := by omega
      refine le_of_eq ?_
      conv_rhs => rw [hT1, Finset.sum_range_succ']
      rw [Nat.add_zero, add_comm]
      exact congrArg (· + ε (size s₀))
        (Finset.sum_congr rfl fun i _ => by congr 1; omega)

/-! ## R1b — answer collisions under fresh uniform draws: `T(T−1)/(2|X|)`

The fresh-uniform model: every query (of arbitrary, adaptively chosen input `a : A`) is
answered by an independent uniform draw from the finite answer space `X`, and the answers
are accumulated in a list. The collision event is `¬ Nodup` on the answer list — *any* two
answers equal, with no input-distinctness side condition (unlike VCVio's
`LogHasCollision`); in the eager-table model repeated inputs return equal answers, so this
fresh-draw event is the conservative upper estimate used by CO25 Lemma 5.8. -/

section FreshUniform

variable (A X : Type) [SampleableType X] [Fintype X] [DecidableEq X]

/-- Fresh-uniform answer oracle with an answer log: every query is answered by a fresh
uniform draw from `X`, recorded at the head of the state list. -/
noncomputable def freshUniformLogImpl : QueryImpl (A →ₒ X) (StateT (List X) ProbComp) :=
  fun _ l => (fun x => (x, x :: l)) <$> ($ᵗ X)

omit [DecidableEq X] in
/-- One fresh uniform draw collides with a duplicate-free answer list `l` with probability
at most `|l|/|X|` (the per-step cost of the birthday accumulator). -/
lemma freshUniformLogImpl_step_collision_le (a : A) (l : List X) (hl : ¬¬ l.Nodup) :
    Pr[ fun us : X × List X => ¬ us.2.Nodup | (freshUniformLogImpl A X a).run l] ≤
      (l.length : ℝ≥0∞) * (Fintype.card X : ℝ≥0∞)⁻¹ := by
  letI : DecidableEq X := Classical.decEq X
  rw [not_not] at hl
  change Pr[ fun us : X × List X => ¬ us.2.Nodup | (fun x => (x, x :: l)) <$> ($ᵗ X)] ≤ _
  rw [probEvent_map]
  refine le_trans (probEvent_mono'' (q := fun x => x ∈ l) fun x hx => ?_) ?_
  · by_contra hmem
    exact hx (List.nodup_cons.mpr ⟨hmem, hl⟩)
  · rw [probEvent_uniformSample, div_eq_mul_inv]
    refine mul_le_mul' ?_ le_rfl
    calc ((Finset.univ.filter (fun x => x ∈ l)).card : ℝ≥0∞)
        ≤ (l.toFinset.card : ℝ≥0∞) := by
          exact_mod_cast Finset.card_le_card fun x hx =>
            List.mem_toFinset.mpr (Finset.mem_filter.mp hx).2
      _ ≤ (l.length : ℝ≥0∞) := by exact_mod_cast l.toFinset_card_le

omit [DecidableEq X] in
/-- R1b (tight) — **adaptive answer-collision birthday bound**: `T` adaptive queries
answered by fresh uniform draws over `X` produce two equal answers with probability at most
`T(T−1)/(2|X|)`. -/
theorem probEvent_collision_freshUniformLog_le_tight {α : Type}
    (oa : OracleComp (A →ₒ X) α) (T : ℕ) (hT : IsTotalQueryBound oa T) :
    Pr[ fun xs : α × List X => ¬ xs.2.Nodup |
        (simulateQ (freshUniformLogImpl A X) oa).run []] ≤
      ((T * (T - 1) : ℕ) : ℝ≥0∞) / (2 * Fintype.card X) := by
  have h := probEvent_simulateQ_stateT_le_sum_of_step
    (impl := freshUniformLogImpl A X)
    (bad := fun l : List X => ¬ l.Nodup) (size := List.length)
    (ε := fun m => (m : ℝ≥0∞) * (Fintype.card X : ℝ≥0∞)⁻¹)
    (fun m₁ m₂ hm => mul_le_mul' (by exact_mod_cast hm) le_rfl)
    (freshUniformLogImpl_step_collision_le A X)
    (fun a l _ us hus => by
      rw [show (freshUniformLogImpl A X a).run l = (fun x => (x, x :: l)) <$> ($ᵗ X) from rfl,
        support_map] at hus
      obtain ⟨x, _, rfl⟩ := hus
      simp)
    T hT [] (by simp)
  refine le_trans h (le_of_eq ?_)
  simp only [List.length_nil, Nat.zero_add]
  exact ENNReal.gauss_sum_inv_eq T _

omit [DecidableEq X] in
/-- R1b — answer-collision birthday bound, squared form `T²/(2|X|)` (the shape consumed by
the CO25 §5.8 claim arithmetic). -/
theorem probEvent_collision_freshUniformLog_le {α : Type}
    (oa : OracleComp (A →ₒ X) α) (T : ℕ) (hT : IsTotalQueryBound oa T) :
    Pr[ fun xs : α × List X => ¬ xs.2.Nodup |
        (simulateQ (freshUniformLogImpl A X) oa).run []] ≤
      ((T : ℝ≥0∞) ^ 2) / (2 * Fintype.card X) := by
  refine le_trans (probEvent_collision_freshUniformLog_le_tight A X oa T hT) ?_
  gcongr
  calc ((T * (T - 1) : ℕ) : ℝ≥0∞) ≤ ((T * T : ℕ) : ℝ≥0∞) := by
        exact_mod_cast Nat.mul_le_mul_left T (Nat.sub_le T 1)
    _ = (T : ℝ≥0∞) ^ 2 := by push_cast; ring

/-! ## R1c — adversarial-set landing: `Tk/|X|`

The target set is indexed by the query input, so the adversary chooses it adaptively (in
the DSFS instantiation: "the fresh capacity segment equals one recorded in the trace so
far", CO25 §5.6). The state is a single flag that latches once any answer lands. -/

/-- Fresh-uniform answer oracle with a landing flag: every query `a` is answered by a fresh
uniform draw from `X`; the Boolean state latches if the answer lands in the
adversarially-chosen target set `S a`. -/
noncomputable def freshUniformHitImpl (S : A → Finset X) :
    QueryImpl (A →ₒ X) (StateT Bool ProbComp) :=
  fun a b => (fun x => (x, b || decide (x ∈ S a))) <$> ($ᵗ X)

/-- R1c — **adaptive landing bound**: across `T` adaptive queries answered by fresh uniform
draws over `X`, some answer lands in the (query-dependent) target set of size at most `k`
with probability at most `Tk/|X|`. -/
theorem probEvent_hit_freshUniformHit_le {α : Type} (S : A → Finset X) (k : ℕ)
    (hS : ∀ a, (S a).card ≤ k)
    (oa : OracleComp (A →ₒ X) α) (T : ℕ) (hT : IsTotalQueryBound oa T) :
    Pr[ fun xs : α × Bool => xs.2 = true |
        (simulateQ (freshUniformHitImpl A X S) oa).run false] ≤
      (T : ℝ≥0∞) * k / Fintype.card X := by
  have h := probEvent_simulateQ_stateT_le_sum_of_step
    (impl := freshUniformHitImpl A X S)
    (bad := fun b : Bool => b = true) (size := fun _ => 0)
    (ε := fun _ => (k : ℝ≥0∞) * (Fintype.card X : ℝ≥0∞)⁻¹)
    (fun _ _ _ => le_rfl)
    (fun a b hb => by
      have hbf : b = false := by simpa using hb
      subst hbf
      change Pr[ fun us : X × Bool => us.2 = true |
        (fun x => (x, false || decide (x ∈ S a))) <$> ($ᵗ X)] ≤ _
      rw [probEvent_map]
      refine le_trans (probEvent_mono'' (q := fun x => x ∈ S a) fun x hx => by
        simpa using hx) ?_
      rw [probEvent_uniformSample, Finset.filter_univ_mem, div_eq_mul_inv]
      exact mul_le_mul' (by exact_mod_cast hS a) le_rfl)
    (fun _ _ _ _ _ => Nat.zero_le _)
    T hT false (by simp)
  refine le_trans h (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, div_eq_mul_inv, mul_assoc]

end FreshUniform

/-! ## R1d — numeric bridges onto the CO25 §5.8 claim bounds

The generic bricks output `ℝ≥0∞` bounds over the actual answer space `X` (for DSFS: the
full sponge-state space, `|X| = |Σ|^n`); the §5.8 claims are real-valued with the capacity
denominator `|Σ|^c ≤ |X|`. These lemmas perform the conversion and identify the in-tree
`claim5_21Bound` as the Lemma 5.8 bound family at the Hyb₀/Hyb₁ trace length. -/

section NumericBridges

variable (U : Type) [SpongeUnit U] [SpongeSize] [Fintype U]

/-- CO25 Lemma 5.8 bound family at trace length `T`: `(7T² − 3T)/(2|Σ|^c)`. -/
noncomputable def lemma5_8Bound (T : ℕ) : ℝ :=
  (7 * (T : ℝ) ^ 2 - 3 * (T : ℝ)) / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)

/-- R1d — the in-tree `claim5_21Bound` (KeyLemmaFoundations F1) **is** the Lemma 5.8 bound
family evaluated at the Hyb₀/Hyb₁ trace length `T = tₕ + 1 + tₚ + L + tₚᵢ`. -/
lemma lemma5_8Bound_eq_claim5_21Bound (tₕ tₚ tₚᵢ L : ℕ) :
    lemma5_8Bound U (tₕ + 1 + tₚ + L + tₚᵢ) = claim5_21Bound U tₕ tₚ tₚᵢ L := rfl

/-- R1d — the tight generic birthday output `T(T−1)/(2|X|)`, over any answer space at least
as large as the capacity space (`|Σ|^c ≤ |X|`, e.g. the sponge-state space `|X| = |Σ|^n`),
is dominated by the real-valued Lemma 5.8 bound. -/
lemma birthday_toReal_le_lemma5_8Bound {cardX : ℕ}
    (hX : Fintype.card U ^ SpongeSize.C ≤ cardX) (T : ℕ) :
    (((T * (T - 1) : ℕ) : ℝ≥0∞) / (2 * cardX)).toReal ≤ lemma5_8Bound U T := by
  have hU : Nonempty U := ⟨0⟩
  have hcard1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < (Fintype.card U : ℝ) ^ SpongeSize.C := by positivity
  have hXR : (Fintype.card U : ℝ) ^ SpongeSize.C ≤ (cardX : ℝ) := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < (cardX : ℝ) := lt_of_lt_of_le hpow hXR
  have htoReal : (((T * (T - 1) : ℕ) : ℝ≥0∞) / (2 * cardX)).toReal
      = ((T * (T - 1) : ℕ) : ℝ) / (2 * (cardX : ℝ)) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  rw [htoReal]
  have hnum : ((T * (T - 1) : ℕ) : ℝ) ≤ 7 * (T : ℝ) ^ 2 - 3 * (T : ℝ) := by
    have h1 : ((T * (T - 1) : ℕ) : ℝ) ≤ (T : ℝ) ^ 2 := by
      have : T * (T - 1) ≤ T * T := Nat.mul_le_mul_left T (Nat.sub_le T 1)
      calc ((T * (T - 1) : ℕ) : ℝ) ≤ ((T * T : ℕ) : ℝ) := by exact_mod_cast this
        _ = (T : ℝ) ^ 2 := by push_cast; ring
    have h2 : (3 : ℝ) * T ≤ 6 * (T : ℝ) ^ 2 := by
      have : 3 * T ≤ 6 * T ^ 2 := by nlinarith [Nat.le_self_pow two_ne_zero T]
      exact_mod_cast this
    linarith
  have hnum0 : (0 : ℝ) ≤ 7 * (T : ℝ) ^ 2 - 3 * (T : ℝ) :=
    le_trans (by positivity) hnum
  unfold lemma5_8Bound
  exact div_le_div₀ hnum0 hnum (by linarith) (by linarith)

/-- R1d — the generic landing output `Tk/|X|`, over any answer space at least as large as
the capacity space, is dominated by the capacity-denominator ratio `Tk/|Σ|^c` (the per-event
summand of the Lemma 5.8 numerator). -/
lemma hit_toReal_le_capacityRatio {cardX : ℕ}
    (hX : Fintype.card U ^ SpongeSize.C ≤ cardX) (T k : ℕ) :
    (((T : ℝ≥0∞) * k / cardX)).toReal ≤
      (T : ℝ) * k / (Fintype.card U : ℝ) ^ SpongeSize.C := by
  have hU : Nonempty U := ⟨0⟩
  have hcard1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℝ) < (Fintype.card U : ℝ) ^ SpongeSize.C := by positivity
  have hXR : (Fintype.card U : ℝ) ^ SpongeSize.C ≤ (cardX : ℝ) := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < (cardX : ℝ) := lt_of_lt_of_le hpow hXR
  have htoReal : (((T : ℝ≥0∞) * k / cardX)).toReal = (T : ℝ) * k / (cardX : ℝ) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_mul]
    norm_num
  rw [htoReal]
  exact div_le_div₀ (by positivity) le_rfl hpow hXR

end NumericBridges

/-! ## R1e — honest bad events are dominated by the trace event `E` (modulo M2)

The CO25 honest bad events (`E_inv`/`E_fork`/`E_time` of `KeyLemmaFoundations`, Defs.
5.11/5.13/5.15) live over the backtrack family `S_BT(tr, s)`; their probability bounds in
the paper go through Lemmas 5.12/5.14/5.16 — "off the trace event `E` none of them occurs"
— and then through Lemma 5.8 for `Pr[E]`. The first reduction is exactly the M2 residual
layer of `KeyLemmaFoundations`; given it, the domination below is unconditional and holds
for **any** distribution of traces and target states (so it applies verbatim to every
hybrid of `KeyLemmaHybrids`). -/

section HonestBadEvents

open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

variable {StmtIn U : Type} [SpongeUnit U] [SpongeSize]

/-- R1e — **honest bad events are dominated by `E`**: given the M2 residuals (CO25 Lemmas
5.12/5.14/5.16 in honest form), for any probabilistic experiment `game` exposing a trace
`tr z` and a target state `st z`, the probability that *some* backtrack family witnesses an
honest bad event is at most the probability of the single trace event `E` (CO25 §5.6).
This channels all three §5.6 bad events into the one event that Lemma 5.8 bounds. -/
theorem probEvent_honestBad_le_probEvent_E
    (h12 : Lemma5_12HonestResidual StmtIn U)
    (h14 : Lemma5_14HonestFalseStatement StmtIn U)
    (h16 : Lemma5_16HonestResidual StmtIn U)
    {β : Type} (game : ProbComp β)
    (tr : β → QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (st : β → CanonicalSpongeState U) :
    Pr[ fun z => ∃ S : Backtrack.S_BT (tr z) (st z),
        E_inv_honest (tr z) (st z) S ∨ E_fork_honest (tr z) (st z) S
          ∨ E_time_honest (tr z) (st z) S | game]
      ≤ Pr[ fun z => E (tr z) | game] := by
  refine probEvent_mono'' fun z hz => ?_
  obtain ⟨S, hS⟩ := hz
  by_contra hE
  rcases hS with h | h | h
  · exact h12 (tr z) (st z) S hE h
  · exact h14 (tr z) (st z) S hE h
  · exact h16 (tr z) (st z) S hE h

/-- R1e, deduped timing route — **honest timing events over the deduplicated base trace are
dominated by raw `E`**. This is the usable replacement boundary for the refuted raw
`Lemma5_16HonestResidual`: once the timing event is stated on `(removeRedundantEntryDS tr).1`,
the fixed-trace M2c closure from `Sponge316` applies under the original raw `¬ E tr`
hypothesis because `E` itself is defined over the same deduplicated base trace. -/
theorem probEvent_dedupTimeHonest_le_probEvent_E
    {β : Type} (game : ProbComp β)
    (tr : β → QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (st : β → CanonicalSpongeState U) :
    Pr[ fun z => ∃ S : Backtrack.S_BT (removeRedundantEntryDS (tr z)).1 (st z),
        E_time_honest (removeRedundantEntryDS (tr z)).1 (st z) S | game]
      ≤ Pr[ fun z => E (tr z) | game] := by
  refine probEvent_mono'' fun z hz => ?_
  obtain ⟨S, hS⟩ := hz
  by_contra hE
  exact (Sponge316.not_e_time_honest_removeRedundantEntryDS_of_not_E_raw
    (tr := tr z) (state := st z) (S := S) hE) hS

/-- R1e, mixed raw/deduped route — raw inverse/fork honest events plus deduped timing
events are dominated by raw `E`. This keeps the true M2a residual plus the legacy M2b
statement and removes the false raw M2c residual from the timing side. -/
theorem probEvent_honestBadDedupTime_le_probEvent_E
    (h12 : Lemma5_12HonestResidual StmtIn U)
    (h14 : Lemma5_14HonestFalseStatement StmtIn U)
    {β : Type} (game : ProbComp β)
    (tr : β → QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (st : β → CanonicalSpongeState U) :
    Pr[ fun z =>
        (∃ S : Backtrack.S_BT (tr z) (st z),
          E_inv_honest (tr z) (st z) S ∨ E_fork_honest (tr z) (st z) S) ∨
        ∃ S : Backtrack.S_BT (removeRedundantEntryDS (tr z)).1 (st z),
          E_time_honest (removeRedundantEntryDS (tr z)).1 (st z) S | game]
      ≤ Pr[ fun z => E (tr z) | game] := by
  refine probEvent_mono'' fun z hz => ?_
  by_contra hE
  rcases hz with hRaw | hTime
  · obtain ⟨S, hS⟩ := hRaw
    rcases hS with hInv | hFork
    · exact h12 (tr z) (st z) S hE hInv
    · exact h14 (tr z) (st z) S hE hFork
  · obtain ⟨S, hS⟩ := hTime
    exact (Sponge316.not_e_time_honest_removeRedundantEntryDS_of_not_E_raw
      (tr := tr z) (state := st z) (S := S) hE) hS

end HonestBadEvents

/-! ## R1f — the open instantiation gap, and the assembly that consumes it -/

section EagerInstantiation

open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

variable (StmtIn U : Type) [SpongeUnit U] [SpongeSize] [Fintype U] [DecidableEq U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]

/-- R1f legacy false statement — **CO25 Lemma 5.8 over the eager `D_𝔖` carrier** as
originally stated over the legacy event `E`: for any `T`-query adversary against the
duplex-sponge challenge oracle answered by the once-sampled `(h, p, p⁻¹)` carrier `D_DS`,
the logged trace realizes the combined §5.6 event `E` with probability at most
`(7T² − 3T)/(2|Σ|^c)`
(= `lemma5_8Bound U T`; at the Hyb₀/Hyb₁ trace length this is `claim5_21Bound`).

**Exact gap to the proven bricks of this file.** The generic bricks bound (i) collisions
among fresh i.i.d. uniform answers and (ii) landings in adaptively-chosen sets, at
`T(T−1)/(2|X|)` and `Tk/|X|`. To conclude Lemma 5.8 one still needs:

1. *Carrier coupling*: `D_DS` answers `p`/`p⁻¹` through one uniform `Equiv.Perm`, not by
   fresh draws — a random-permutation/random-function switch (≤ `T(T−1)/(2|X|)` itself, by
   the standard PRP/PRF argument) or a direct without-replacement count is required before
   the fresh-uniform bricks apply; repeated queries answer consistently (eager table), so
   the dedup'd trace (`removeRedundantEntryDS`) must mediate.
2. *Event decomposition*: `E = E_dup ∨ E_func` (CO25 §5.6) must be split into the
   capacity-segment collision/landing families counted by the `7T²` numerator — each
   family is a projection (`capacitySegment`) of a fresh draw landing in a trace-indexed
   set of size ≤ `(#prior entries)·|Σ|^r`, which is precisely shape (ii) with the
   `hit_toReal_le_capacityRatio` conversion, plus the `ψ`-image union for the hash side.
3. *Budget split*: the per-flavor budgets `tₕ/tₚ/tₚᵢ` of the Key-Lemma surface must be
   recombined into the total trace length (`IsTotalQueryBound`), including the verifier's
   `+1` hash query and `≤ L` permutation queries (CO25 Lemma 5.8 is applied at
   `T = tₕ + 1 + tₚ + L + tₚᵢ` — see `lemma5_8Bound_eq_claim5_21Bound`).

**Audit (2026-06-10): REFUTED as stated** —
`Sponge314.K1.lemma5_8EagerBirthdayFalseStatement_false` (Lemma58EagerFalse.lean) exhibits a
single-inverse-query countermodel with `Pr[E] = 1 > lemma5_8Bound U 1`. Root cause is the
B1 defect of `capacitySegmentDupPermInv` (BadEvents.lean): its 5th disjunct anchors on the
**answer** capacity at `j' ≤ j` and self-fires at `j' = j`, so `E` holds on any trace with
a `p⁻¹` entry (`Sponge316.hasInvEntry_implies_E`); CO25 Eq. 26 anchors on the **input**
capacity. The CO25-faithful repaired event and re-statement are the active #314 wave-4
work; the steps 1–3 above describe the proof plan against the *repaired* event. -/
def Lemma5_8EagerBirthdayFalseStatement : Prop :=
  ∀ {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ),
    IsTotalQueryBound P T →
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => E z.2 |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ lemma5_8Bound U T

variable {StmtIn U}

/-- R1 assembly — **honest bad events obey the birthday bound, modulo the named
residuals**: the M2 residuals (CO25 Lemmas 5.12/5.14/5.16, honest form) and the Lemma 5.8
eager residual together bound the probability that the logged trace of the eager
`D_𝔖`-carrier game carries a backtrack family witnessing `E_inv ∨ E_fork ∨ E_time` by
`lemma5_8Bound U T` — which at the Hyb₀/Hyb₁ trace length is exactly `claim5_21Bound`
(`lemma5_8Bound_eq_claim5_21Bound`). This is the CO25 §5.6 → §5.8 channel: prove the four
residuals and the bad-event side of the Hyb₀₁ step is numerically closed. -/
theorem honestBad_birthday_of_residuals
    (h12 : Lemma5_12HonestResidual StmtIn U)
    (h14 : Lemma5_14HonestFalseStatement StmtIn U)
    (h16 : Lemma5_16HonestResidual StmtIn U)
    (h58 : Lemma5_8EagerBirthdayFalseStatement StmtIn U)
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) (st₀ : CanonicalSpongeState U) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        ∃ S : Backtrack.S_BT z.2 st₀,
          E_inv_honest z.2 st₀ S ∨ E_fork_honest z.2 st₀ S ∨ E_time_honest z.2 st₀ S |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ lemma5_8Bound U T := by
  refine le_trans (ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one) ?_) (h58 P T hT)
  exact probEvent_honestBad_le_probEvent_E h12 h14 h16 _
    (fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => z.2) (fun _ => st₀)

/-- R1 assembly, deduped timing lane — assuming the eager birthday residual for raw `E`, the
probability of an honest timing event over the deduplicated logged trace is bounded by
`lemma5_8Bound`. This avoids consuming the refuted raw `Lemma5_16HonestResidual`. -/
theorem dedupTimeHonest_birthday_of_residual
    (h58 : Lemma5_8EagerBirthdayFalseStatement StmtIn U)
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) (st₀ : CanonicalSpongeState U) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        ∃ S : Backtrack.S_BT (removeRedundantEntryDS z.2).1 st₀,
          E_time_honest (removeRedundantEntryDS z.2).1 st₀ S |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ lemma5_8Bound U T := by
  refine le_trans (ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one) ?_) (h58 P T hT)
  exact probEvent_dedupTimeHonest_le_probEvent_E _
    (fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => z.2) (fun _ => st₀)

/-- R1 assembly, mixed raw/deduped route — M2a/M2b for raw inverse/fork events plus the
deduped timing lane and the eager birthday residual imply the birthday bound. This is the
assembly counterpart of `probEvent_honestBadDedupTime_le_probEvent_E` and avoids the refuted
raw M2c hypothesis. -/
theorem honestBadDedupTime_birthday_of_residuals
    (h12 : Lemma5_12HonestResidual StmtIn U)
    (h14 : Lemma5_14HonestFalseStatement StmtIn U)
    (h58 : Lemma5_8EagerBirthdayFalseStatement StmtIn U)
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) (st₀ : CanonicalSpongeState U) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        (∃ S : Backtrack.S_BT z.2 st₀,
          E_inv_honest z.2 st₀ S ∨ E_fork_honest z.2 st₀ S) ∨
        ∃ S : Backtrack.S_BT (removeRedundantEntryDS z.2).1 st₀,
          E_time_honest (removeRedundantEntryDS z.2).1 st₀ S |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ lemma5_8Bound U T := by
  refine le_trans (ENNReal.toReal_mono
    (ne_top_of_le_ne_top ENNReal.one_ne_top probEvent_le_one) ?_) (h58 P T hT)
  exact probEvent_honestBadDedupTime_le_probEvent_E h12 h14 _
    (fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => z.2) (fun _ => st₀)

end EagerInstantiation

end DuplexSpongeFS.BirthdayBound

#print axioms DuplexSpongeFS.BirthdayBound.probEvent_simulateQ_stateT_le_sum_of_step
#print axioms DuplexSpongeFS.BirthdayBound.freshUniformLogImpl_step_collision_le
#print axioms DuplexSpongeFS.BirthdayBound.probEvent_collision_freshUniformLog_le_tight
#print axioms DuplexSpongeFS.BirthdayBound.probEvent_collision_freshUniformLog_le
#print axioms DuplexSpongeFS.BirthdayBound.probEvent_hit_freshUniformHit_le
#print axioms DuplexSpongeFS.BirthdayBound.lemma5_8Bound_eq_claim5_21Bound
#print axioms DuplexSpongeFS.BirthdayBound.birthday_toReal_le_lemma5_8Bound
#print axioms DuplexSpongeFS.BirthdayBound.hit_toReal_le_capacityRatio
#print axioms DuplexSpongeFS.BirthdayBound.probEvent_honestBad_le_probEvent_E
#print axioms DuplexSpongeFS.BirthdayBound.probEvent_dedupTimeHonest_le_probEvent_E
#print axioms DuplexSpongeFS.BirthdayBound.probEvent_honestBadDedupTime_le_probEvent_E
#print axioms DuplexSpongeFS.BirthdayBound.honestBad_birthday_of_residuals
#print axioms DuplexSpongeFS.BirthdayBound.dedupTimeHonest_birthday_of_residual
#print axioms DuplexSpongeFS.BirthdayBound.honestBadDedupTime_birthday_of_residuals

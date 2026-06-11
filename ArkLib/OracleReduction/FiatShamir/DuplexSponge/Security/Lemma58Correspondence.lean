/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma58Flag
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEvents

/-!
# The log–cache–flag correspondence (CO25 Lemma 5.8, the support-level carrier)

The engine output (`Lemma58Flag.lean`) bounds the probability of the ghost flag; the paper
event `EPaper` lives on the *query log* of the logged run. This file connects them at the
support level. The three log-indexed folds:

* `stepCache` / `cacheOfLog` — the cache is a deterministic fold of the log (first
  occurrence wins; hits change nothing);
* `ConsistentFrom` — every logged answer agrees with the cache at its position (the lazy
  oracle memoizes, so its logs are consistent);
* `AnchoredFrom` — some logged step was fresh and its sampled answer's capacity hit an
  existing slot or its own query's capacity (`collisionStep`).

The master run induction (`support_flagged_logged`) shows every support element of the
flagged run of the logged program satisfies: final cache = fold of the log, the log is
consistent, and the final flag is *exactly* `initial ∨ AnchoredFrom`. The pure
combinatorial part (`¬Anchored ∧ Consistent → ¬EPaper`, via the dedup characterization)
follows in this file's later sections.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (see `#print axioms` at EOF).
-/

open OracleComp OracleSpec
open scoped ENNReal NNReal

namespace DuplexSpongeFS.EagerLazyDS

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn]
  [SampleableType (Vector U SpongeSize.C)]
  [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]
  [Fintype StmtIn] [Fintype U] [DecidableEq U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]

/-- A single log entry of the combined oracle. -/
abbrev DSEntry (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Type :=
  (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
    (duplexSpongeChallengeOracle StmtIn U).Range t

/-- Fold one log entry onto a cache: first occurrence caches, repeats change nothing. -/
def stepCache (c : DSCache StmtIn U) : DSEntry StmtIn U → DSCache StmtIn U
  | ⟨.inl q, u⟩ =>
      match c.1 q with
      | none => (c.1.cacheQuery q u, c.2)
      | some _ => c
  | ⟨.inr (.inl a), b⟩ =>
      match c.2.find? (fun w => w.1 = a) with
      | none => (c.1, c.2.concat (a, b))
      | some _ => c
  | ⟨.inr (.inr b), a⟩ =>
      match c.2.find? (fun w => w.2 = b) with
      | none => (c.1, c.2.concat (a, b))
      | some _ => c

/-- A log entry agrees with a cache: if its query is cached, the logged answer is the
cached one. -/
def entryConsistent (c : DSCache StmtIn U) : DSEntry StmtIn U → Prop
  | ⟨.inl q, u⟩ => ∀ u', c.1 q = some u' → u = u'
  | ⟨.inr (.inl a), b⟩ => ∀ w, c.2.find? (fun w => w.1 = a) = some w → b = w.2
  | ⟨.inr (.inr b), a⟩ => ∀ w, c.2.find? (fun w => w.2 = b) = some w → a = w.1

/-- The whole log is consistent with the running cache. -/
def ConsistentFrom (c : DSCache StmtIn U) : List (DSEntry StmtIn U) → Prop
  | [] => True
  | e :: ℓ => entryConsistent c e ∧ ConsistentFrom (stepCache c e) ℓ

/-- Some entry of the log is an anchored collision against the running cache. -/
def AnchoredFrom (c : DSCache StmtIn U) : List (DSEntry StmtIn U) → Prop
  | [] => False
  | e :: ℓ => collisionStep e.1 c e.2 ∨ AnchoredFrom (stepCache c e) ℓ

/-- **The per-step support facts**: each reachable one-step outcome of the flagged oracle
has the folded cache, a consistent entry, and the exact flag update. -/
theorem lazyDSImplFlagged_step_support
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) (s : DSCache StmtIn U × Prop) :
    ∀ us ∈ support ((lazyDSImplFlagged t).run s),
      us.2.1 = stepCache s.1 ⟨t, us.1⟩ ∧ entryConsistent s.1 ⟨t, us.1⟩ ∧
        (us.2.2 ↔ (s.2 ∨ collisionStep t s.1 us.1)) := by
  classical
  obtain ⟨⟨ch, cp⟩, fl⟩ := s
  intro us hus
  rw [lazyDSImplFlagged_run] at hus
  simp only [support_map, Set.mem_image] at hus
  obtain ⟨w, hw, rfl⟩ := hus
  refine ⟨?_, ?_, Iff.rfl⟩ <;> rcases t with q | sIn | sOut
  · -- hash arm, cache shape
    rcases hcq : ch q with _ | u
    · rw [lazyDSImpl_run_hash, QueryImpl.withCaching_run_none _ hcq, Functor.map_map] at hw
      have hw' : w ∈ support ((fun a => (a, (ch.cacheQuery q a, cp))) <$>
          ($ᵗ (Vector U SpongeSize.C))) := hw
      simp only [support_map, Set.mem_image] at hw'
      obtain ⟨u, _, rfl⟩ := hw'
      simp [stepCache, hcq]
    · rw [lazyDSImpl_run_hash, QueryImpl.withCaching_run_some _ hcq, map_pure] at hw
      have hw2 : w = ((u : Vector U SpongeSize.C), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      simp [stepCache, hcq]
  · rcases hcfind : cp.find? (fun w => w.1 = sIn) with _ | w₀
    · rw [lazyDSImpl_run_fwd, LazyPermBridge.lazyPermImpl_run_inl_none cp hcfind,
        Functor.map_map] at hw
      have hw' : w ∈ support ((fun b => (b, (ch, cp.concat (sIn, b)))) <$>
          LazyPermBridge.sampleUnused (LazyPermBridge.unusedValuesList cp)) := hw
      simp only [support_map, Set.mem_image] at hw'
      obtain ⟨b, _, rfl⟩ := hw'
      simp [stepCache, hcfind]
    · rw [lazyDSImpl_run_fwd, LazyPermBridge.lazyPermImpl_run_inl_some cp hcfind,
        map_pure] at hw
      have hw2 : w = ((w₀.2 : CanonicalSpongeState U), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      simp [stepCache, hcfind]
  · rcases hcfind : cp.find? (fun w => w.2 = sOut) with _ | w₀
    · rw [lazyDSImpl_run_inv, LazyPermBridge.lazyPermImpl_run_inr_none cp hcfind,
        Functor.map_map] at hw
      have hw' : w ∈ support ((fun a => (a, (ch, cp.concat (a, sOut)))) <$>
          LazyPermBridge.sampleUnused (LazyPermBridge.unusedKeysList cp)) := hw
      simp only [support_map, Set.mem_image] at hw'
      obtain ⟨a, _, rfl⟩ := hw'
      simp [stepCache, hcfind]
    · rw [lazyDSImpl_run_inv, LazyPermBridge.lazyPermImpl_run_inr_some cp hcfind,
        map_pure] at hw
      have hw2 : w = ((w₀.1 : CanonicalSpongeState U), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      simp [stepCache, hcfind]
  · -- hash arm, consistency
    rcases hcq : ch q with _ | u
    · intro u' hu'
      replace hu' : ch q = some u' := hu'
      rw [hcq] at hu'
      exact absurd hu' (by simp)
    · rw [lazyDSImpl_run_hash, QueryImpl.withCaching_run_some _ hcq, map_pure] at hw
      have hw2 : w = ((u : Vector U SpongeSize.C), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      intro u' hu'
      replace hu' : ch q = some u' := hu'
      rw [hcq] at hu'
      exact Option.some_inj.mp hu'
  · rcases hcfind : cp.find? (fun w => w.1 = sIn) with _ | w₀
    · intro w' hw'
      replace hw' : cp.find? (fun w => w.1 = sIn) = some w' := hw'
      rw [hcfind] at hw'
      exact absurd hw' (by simp)
    · rw [lazyDSImpl_run_fwd, LazyPermBridge.lazyPermImpl_run_inl_some cp hcfind,
        map_pure] at hw
      have hw2 : w = ((w₀.2 : CanonicalSpongeState U), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      intro w' hw'
      replace hw' : cp.find? (fun w => w.1 = sIn) = some w' := hw'
      rw [hcfind] at hw'
      rw [Option.some_inj.mp hw']
  · rcases hcfind : cp.find? (fun w => w.2 = sOut) with _ | w₀
    · intro w' hw'
      replace hw' : cp.find? (fun w => w.2 = sOut) = some w' := hw'
      rw [hcfind] at hw'
      exact absurd hw' (by simp)
    · rw [lazyDSImpl_run_inv, LazyPermBridge.lazyPermImpl_run_inr_some cp hcfind,
        map_pure] at hw
      have hw2 : w = ((w₀.1 : CanonicalSpongeState U), ((ch, cp) : DSCache StmtIn U)) := hw
      subst hw2
      intro w' hw'
      replace hw' : cp.find? (fun w => w.2 = sOut) = some w' := hw'
      rw [hcfind] at hw'
      rw [Option.some_inj.mp hw']

/-- **The master run correspondence**: every support element of the flagged run of the
logged program has its final cache equal to the fold of its log, a consistent log, and a
final flag exactly `initial ∨ AnchoredFrom`. -/
theorem support_flagged_logged {α : Type}
    (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α)
    (c₀ : DSCache StmtIn U) (fl₀ : Prop) :
    ∀ xs ∈ support ((simulateQ lazyDSImplFlagged
        ((simulateQ loggingOracle P).run)).run (c₀, fl₀)),
      xs.2.1 = xs.1.2.foldl stepCache c₀ ∧
      ConsistentFrom c₀ xs.1.2 ∧
      (xs.2.2 ↔ (fl₀ ∨ AnchoredFrom c₀ xs.1.2)) := by
  induction P using OracleComp.inductionOn generalizing c₀ fl₀ with
  | pure a =>
      intro xs hxs
      rw [show ((simulateQ loggingOracle (pure a :
            OracleComp (duplexSpongeChallengeOracle StmtIn U) α)).run)
          = pure (a, ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U))) from by
        simp [simulateQ_pure]] at hxs
      rw [simulateQ_pure, StateT.run_pure] at hxs
      have hxs2 : xs = ((a, ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U))),
          (c₀, fl₀)) := by
        have hxs' : xs ∈ support ((pure ((a,
            ([] : QueryLog (duplexSpongeChallengeOracle StmtIn U))),
            (c₀, fl₀)) : ProbComp _)) := hxs
        rw [support_pure] at hxs'
        exact hxs'
      subst hxs2
      exact ⟨rfl, trivial, by tauto⟩
  | query_bind t k ih =>
      intro xs hxs
      rw [OracleComp.run_simulateQ_loggingOracle_query_bind] at hxs
      rw [simulateQ_bind, StateT.run_bind] at hxs
      rw [show (simulateQ lazyDSImplFlagged
            (liftM ((duplexSpongeChallengeOracle StmtIn U).query t))).run (c₀, fl₀)
          = (lazyDSImplFlagged t).run (c₀, fl₀) from by
        refine congrArg (fun z => StateT.run z (c₀, fl₀)) ?_
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query,
          id_map]] at hxs
      obtain ⟨us, hus, hxs2⟩ := (mem_support_bind_iff _ _ _).1 hxs
      obtain ⟨hcache, hcons, hflag⟩ := lazyDSImplFlagged_step_support t (c₀, fl₀) us hus
      rw [simulateQ_map, StateT.run_map] at hxs2
      simp only [support_map, Set.mem_image] at hxs2
      obtain ⟨w, hw, rfl⟩ := hxs2
      obtain ⟨ih1, ih2, ih3⟩ := ih us.1 us.2.1 us.2.2 w hw
      refine ⟨?_, ⟨hcons, ?_⟩, ?_⟩
      · rw [List.foldl_cons, ← hcache]
        exact ih1
      · rw [← hcache]
        exact ih2
      · rw [show AnchoredFrom c₀
            ((⟨t, us.1⟩ : DSEntry StmtIn U) :: w.1.2)
            = (collisionStep t c₀ us.1 ∨ AnchoredFrom (stepCache c₀ ⟨t, us.1⟩) w.1.2)
          from rfl, ← hcache]
        rw [ih3, hflag]
        tauto

/-! ## The entry-class structure (pure list combinatorics)

CO25's redundancy certificates partition entries into classes of size at most two:
a hash entry is its own class; a permutation entry is classed with its opposite-direction
swap. The dedup procedure keeps exactly the first occurrence of each class. -/

/-- The opposite-direction form of an entry (hash entries are self-paired). -/
def swapEntry : DSEntry StmtIn U → DSEntry StmtIn U
  | ⟨.inl q, u⟩ => ⟨.inl q, u⟩
  | ⟨.inr (.inl a), b⟩ => ⟨.inr (.inr b), a⟩
  | ⟨.inr (.inr b), a⟩ => ⟨.inr (.inl a), b⟩

@[simp] lemma swapEntry_swapEntry (e : DSEntry StmtIn U) :
    swapEntry (swapEntry e) = e := by
  rcases e with ⟨t, ans⟩
  rcases t with q | sIn | sOut <;> rfl

/-- Class membership: equal or the swap. -/
def sameClass (e e' : DSEntry StmtIn U) : Prop :=
  e' = e ∨ e' = swapEntry e

lemma sameClass_refl (e : DSEntry StmtIn U) : sameClass e e := Or.inl rfl

lemma sameClass_symm {e e' : DSEntry StmtIn U} (h : sameClass e e') : sameClass e' e := by
  rcases h with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (swapEntry_swapEntry e).symm

lemma sameClass_trans {e₁ e₂ e₃ : DSEntry StmtIn U}
    (h₁ : sameClass e₁ e₂) (h₂ : sameClass e₂ e₃) : sameClass e₁ e₃ := by
  rcases h₁ with rfl | rfl
  · exact h₂
  · rcases h₂ with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (swapEntry_swapEntry e₁)

/-- The paper redundancy predicate is exactly "an earlier class member exists". -/
lemma redundantEntryDSPaper_iff_sameClass
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin log.length) :
    DuplexSpongeFS.Paper.redundantEntryDSPaper log idx
      ↔ ∃ j' < idx, sameClass log[idx] log[j'] := by
  unfold DuplexSpongeFS.Paper.redundantEntryDSPaper
  rcases hidx : log[idx] with ⟨t, ans⟩
  rcases t with q | sIn | sOut
  · constructor
    · rintro ⟨j', hj', hej'⟩
      exact ⟨j', hj', Or.inl hej'⟩
    · rintro ⟨j', hj', hcl | hcl⟩
      · exact ⟨j', hj', hcl⟩
      · exact ⟨j', hj', hcl⟩
  · constructor
    · rintro ⟨j', hj', hej'⟩
      rcases hej' with h | h
      · exact ⟨j', hj', Or.inl h⟩
      · exact ⟨j', hj', Or.inr h⟩
    · rintro ⟨j', hj', hcl | hcl⟩
      · exact ⟨j', hj', Or.inl hcl⟩
      · exact ⟨j', hj', Or.inr hcl⟩
  · constructor
    · rintro ⟨j', hj', hej'⟩
      rcases hej' with h | h
      · exact ⟨j', hj', Or.inl h⟩
      · exact ⟨j', hj', Or.inr h⟩
    · rintro ⟨j', hj', hcl | hcl⟩
      · exact ⟨j', hj', Or.inl hcl⟩
      · exact ⟨j', hj', Or.inr hcl⟩

/-! ## Fold monotonicity primitives -/

/-- The permutation cache only grows (as a sublist) along one fold step. -/
theorem stepCache_perm_sublist (c : DSCache StmtIn U) (e : DSEntry StmtIn U) :
    c.2.Sublist (stepCache c e).2 := by
  rcases e with ⟨t, ans⟩
  rcases t with q | a | b
  · rcases hcq : c.1 q with _ | u <;> simp [stepCache, hcq]
  · rcases hf : c.2.find? (fun w => w.1 = a) with _ | w <;>
      simp only [stepCache, hf]
    · rw [List.concat_eq_append]; exact List.sublist_append_left _ _
    · exact List.Sublist.refl _
  · rcases hf : c.2.find? (fun w => w.2 = b) with _ | w <;>
      simp only [stepCache, hf]
    · rw [List.concat_eq_append]; exact List.sublist_append_left _ _
    · exact List.Sublist.refl _

/-- The hash cache only grows: an already-cached answer survives one fold step. -/
theorem stepCache_hash_mono (c : DSCache StmtIn U) (e : DSEntry StmtIn U)
    {q : StmtIn} {u : Vector U SpongeSize.C} (h : c.1 q = some u) :
    (stepCache c e).1 q = some u := by
  rcases e with ⟨t, ans⟩
  rcases t with q' | a | b
  · rcases hcq : c.1 q' with _ | u' <;> simp only [stepCache, hcq]
    · rcases eq_or_ne q q' with rfl | hne
      · rw [hcq] at h; exact absurd h (by simp)
      · rw [OracleSpec.QueryCache.cacheQuery_of_ne _ _ hne]; exact h
    · exact h
  · rcases hf : c.2.find? (fun w => w.1 = a) with _ | w <;> simp only [stepCache, hf] <;> exact h
  · rcases hf : c.2.find? (fun w => w.2 = b) with _ | w <;> simp only [stepCache, hf] <;> exact h

/-- The permutation cache only grows along the whole fold. -/
theorem foldl_stepCache_perm_sublist (c : DSCache StmtIn U) (L : List (DSEntry StmtIn U)) :
    c.2.Sublist (L.foldl stepCache c).2 := by
  induction L generalizing c with
  | nil => exact List.Sublist.refl _
  | cons e ℓ ih =>
      rw [List.foldl_cons]
      exact (stepCache_perm_sublist c e).trans (ih (stepCache c e))

/-! ## Key-existence characterization of the fold (consistency-free) -/

/-- Whether a permutation cache already holds the forward key `a`. -/
def hasFwdKey (c : DSCache StmtIn U) (a : CanonicalSpongeState U) : Prop :=
  ∃ w ∈ c.2, w.1 = a

/-- Whether a permutation cache already holds the inverse key `b`. -/
def hasInvKey (c : DSCache StmtIn U) (b : CanonicalSpongeState U) : Prop :=
  ∃ w ∈ c.2, w.2 = b

/-- The forward key inserted by an entry (`none` for a hash entry). -/
def entryFwdKey : DSEntry StmtIn U → Option (CanonicalSpongeState U)
  | ⟨.inl _, _⟩ => none
  | ⟨.inr (.inl a), _⟩ => some a
  | ⟨.inr (.inr _), a⟩ => some a

/-- The inverse key inserted by an entry (`none` for a hash entry). For a forward entry
`⟨inr (inl a), b⟩` the inserted pair is `(a, b)` so the inverse key is its answer `b`; for an
inverse entry `⟨inr (inr b), a⟩` the inserted pair is `(a, b)` so the inverse key is its
query `b`. -/
def entryInvKey : DSEntry StmtIn U → Option (CanonicalSpongeState U)
  | ⟨.inl _, _⟩ => none
  | ⟨.inr (.inl _), b⟩ => some b
  | ⟨.inr (.inr b), _⟩ => some b

/-- One fold step can only create the inverse key it inserts (sound direction only). -/
theorem hasInvKey_stepCache_imp (c : DSCache StmtIn U) (e : DSEntry StmtIn U)
    (b : CanonicalSpongeState U) (h : hasInvKey (stepCache c e) b) :
    hasInvKey c b ∨ entryInvKey e = some b := by
  rcases e with ⟨t, ans⟩
  rcases t with q | a' | b'
  · -- hash entry: perm cache unchanged
    left
    obtain ⟨w, hw, hwb⟩ := h
    rcases hcq : c.1 q with _ | u
    · exact ⟨w, by simpa [stepCache, hcq] using hw, hwb⟩
    · exact ⟨w, by simpa [stepCache, hcq] using hw, hwb⟩
  · -- forward entry inserts pair (a', ans); inverse key = ans
    rcases hf : c.2.find? (fun w => w.1 = a') with _ | w
    · obtain ⟨w, hw, rfl⟩ := h
      simp only [stepCache, hf] at hw
      rw [List.concat_eq_append, List.mem_append] at hw
      rcases hw with hw | hw
      · exact Or.inl ⟨w, hw, rfl⟩
      · simp only [List.mem_singleton] at hw; subst hw; exact Or.inr rfl
    · left
      obtain ⟨w', hw', hwb'⟩ := h
      exact ⟨w', by simpa [stepCache, hf] using hw', hwb'⟩
  · -- inverse entry inserts pair (ans, b'); inverse key = b'
    rcases hf : c.2.find? (fun w => w.2 = b') with _ | w
    · obtain ⟨w, hw, rfl⟩ := h
      simp only [stepCache, hf] at hw
      rw [List.concat_eq_append, List.mem_append] at hw
      rcases hw with hw | hw
      · exact Or.inl ⟨w, hw, rfl⟩
      · simp only [List.mem_singleton] at hw; subst hw; exact Or.inr rfl
    · left
      obtain ⟨w', hw', hwb'⟩ := h
      exact ⟨w', by simpa [stepCache, hf] using hw', hwb'⟩

/-- One fold step can only create the forward key it inserts: if a key is present after the
step but not before, the step's entry inserts exactly that key. (The reverse is false for
cache *hits* without a consistency assumption, so only this sound direction is stated.) -/
theorem hasFwdKey_stepCache_imp (c : DSCache StmtIn U) (e : DSEntry StmtIn U)
    (a : CanonicalSpongeState U) (h : hasFwdKey (stepCache c e) a) :
    hasFwdKey c a ∨ entryFwdKey e = some a := by
  rcases e with ⟨t, ans⟩
  rcases t with q | a' | b'
  · -- hash entry: perm cache unchanged
    left
    obtain ⟨w, hw, hwa⟩ := h
    rcases hcq : c.1 q with _ | u
    · exact ⟨w, by simpa [stepCache, hcq] using hw, hwa⟩
    · exact ⟨w, by simpa [stepCache, hcq] using hw, hwa⟩
  · -- forward entry inserts pair (a', ans)
    rcases hf : c.2.find? (fun w => w.1 = a') with _ | w
    · obtain ⟨w, hw, rfl⟩ := h
      simp only [stepCache, hf] at hw
      rw [List.concat_eq_append, List.mem_append] at hw
      rcases hw with hw | hw
      · exact Or.inl ⟨w, hw, rfl⟩
      · simp only [List.mem_singleton] at hw; subst hw; exact Or.inr rfl
    · left
      obtain ⟨w', hw', hwa'⟩ := h
      exact ⟨w', by simpa [stepCache, hf] using hw', hwa'⟩
  · -- inverse entry inserts pair (ans, b')
    rcases hf : c.2.find? (fun w => w.2 = b') with _ | w
    · obtain ⟨w, hw, rfl⟩ := h
      simp only [stepCache, hf] at hw
      rw [List.concat_eq_append, List.mem_append] at hw
      rcases hw with hw | hw
      · exact Or.inl ⟨w, hw, rfl⟩
      · simp only [List.mem_singleton] at hw; subst hw; exact Or.inr rfl
    · left
      obtain ⟨w', hw', hwa'⟩ := h
      exact ⟨w', by simpa [stepCache, hf] using hw', hwa'⟩

/-- A forward key present after the whole fold was either present at the start or inserted
by some entry of the log. -/
theorem hasFwdKey_foldl_imp (c : DSCache StmtIn U) (L : List (DSEntry StmtIn U))
    (a : CanonicalSpongeState U) (h : hasFwdKey (L.foldl stepCache c) a) :
    hasFwdKey c a ∨ ∃ e ∈ L, entryFwdKey e = some a := by
  induction L generalizing c with
  | nil => exact Or.inl h
  | cons e ℓ ih =>
      rw [List.foldl_cons] at h
      rcases ih (stepCache c e) h with h' | ⟨e', he', hk'⟩
      · rcases hasFwdKey_stepCache_imp c e a h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr ⟨e, List.mem_cons_self, h''⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hk'⟩

/-- An inverse key present after the whole fold was present at the start or inserted by
some entry of the log. -/
theorem hasInvKey_foldl_imp (c : DSCache StmtIn U) (L : List (DSEntry StmtIn U))
    (b : CanonicalSpongeState U) (h : hasInvKey (L.foldl stepCache c) b) :
    hasInvKey c b ∨ ∃ e ∈ L, entryInvKey e = some b := by
  induction L generalizing c with
  | nil => exact Or.inl h
  | cons e ℓ ih =>
      rw [List.foldl_cons] at h
      rcases ih (stepCache c e) h with h' | ⟨e', he', hk'⟩
      · rcases hasInvKey_stepCache_imp c e b h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr ⟨e, List.mem_cons_self, h''⟩
      · exact Or.inr ⟨e', List.mem_cons_of_mem _ he', hk'⟩

/-! ## Dedup preserves every class (piece A1) -/

open DuplexSpongeFS.Paper in
/-- **Dedup is a system of class representatives**: every entry of the raw log has a
class-representative surviving in the dedup output. (The output is also pairwise
class-distinct, so it is exactly one representative per class.) -/
theorem mem_imp_sameClass_mem_removeRedundant
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (e : DSEntry StmtIn U) (he : e ∈ log) :
    ∃ e' ∈ (removeRedundantEntryDSPaper log).1, sameClass e e' := by
  letI : Decidable (∃ idx : Fin log.length,
      DuplexSpongeFS.Paper.redundantEntryDSPaper log idx) := Classical.propDecidable _
  rw [removeRedundantEntryDSPaper]
  by_cases h : ∃ idx : Fin log.length, redundantEntryDSPaper log idx
  · rw [dif_pos h]
    set i := (Classical.choose h).val with hi
    have hilt : i < log.length := (Classical.choose h).isLt
    by_cases hmem : e ∈ log.eraseIdx i
    · obtain ⟨e'', hmem'', hcl''⟩ :=
        mem_imp_sameClass_mem_removeRedundant (log.eraseIdx i) e hmem
      exact ⟨e'', hmem'', hcl''⟩
    · -- e ∈ log but not in eraseIdx i: every occurrence of e is at index i, so e = log[i]
      have hek : e = log[i] := by
        obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
        by_cases hki : k = i
        · subst hki; exact hke.symm
        · exact absurd (List.mem_eraseIdx_iff_getElem.mpr ⟨k, hk, hki, hke⟩) hmem
      -- log[i] is redundant: it has an earlier same-class witness at j' ≠ i
      have hred : redundantEntryDSPaper log (Classical.choose h) := Classical.choose_spec h
      obtain ⟨j', hj', hclj'⟩ :=
        (redundantEntryDSPaper_iff_sameClass log (Classical.choose h)).mp hred
      have hj'i : (j' : ℕ) ≠ i := by
        rw [hi]; exact Nat.ne_of_lt hj'
      have hwitmem : log[(j' : ℕ)] ∈ log.eraseIdx i :=
        List.mem_eraseIdx_iff_getElem.mpr ⟨(j' : ℕ), j'.isLt, hj'i, rfl⟩
      obtain ⟨e'', hmem'', hcl''⟩ :=
        mem_imp_sameClass_mem_removeRedundant (log.eraseIdx i) log[(j' : ℕ)] hwitmem
      refine ⟨e'', hmem'', ?_⟩
      -- sameClass e log[j'] from hclj' (sameClass log[i] log[j']) and e = log[i]
      have hcl_e : sameClass e log[(j' : ℕ)] := by
        rw [hek]; exact hclj'
      exact sameClass_trans hcl_e hcl''
  · rw [dif_neg h]
    exact ⟨e, he, sameClass_refl e⟩
termination_by log.length
decreasing_by
  all_goals
    have hlt : (Classical.choose h).val < log.length := (Classical.choose h).isLt
    have heq : (log.eraseIdx (Classical.choose h).val).length + 1 = log.length :=
      List.length_eraseIdx_add_one hlt
    omega

/-! ## Key pair pins the class -/

/-- An entry whose inserted pair is `(a, b)` is class-equal to the forward entry
`⟨inr (inl a), b⟩`: it is either that entry or its inverse swap. -/
theorem sameClass_of_entryKeys
    {e' : DSEntry StmtIn U} {a b : CanonicalSpongeState U}
    (hf : entryFwdKey e' = some a) (hi : entryInvKey e' = some b) :
    sameClass (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U) e' := by
  rcases e' with ⟨t, ans⟩
  rcases t with q | a' | b'
  · simp only [entryFwdKey] at hf; exact absurd hf (by simp)
  · -- forward ⟨inr (inl a'), ans⟩: fwd-key a', inv-key ans
    simp only [entryFwdKey] at hf
    simp only [entryInvKey] at hi
    rw [Option.some_inj] at hf hi
    subst hf; subst hi
    exact Or.inl rfl
  · -- inverse ⟨inr (inr b'), ans⟩: fwd-key ans, inv-key b'
    simp only [entryFwdKey] at hf
    simp only [entryInvKey] at hi
    rw [Option.some_inj] at hf hi
    subst hf; subst hi
    -- e' = ⟨inr (inr b), a⟩ = swapEntry ⟨inr (inl a), b⟩
    exact Or.inr rfl

/-! ## Capacity-freshness from non-anchoredness (piece B) -/

/-- Cons-unfolding of `¬ AnchoredFrom`: no step of `e :: ℓ` is an anchored collision. -/
theorem not_anchoredFrom_cons {c : DSCache StmtIn U} {e : DSEntry StmtIn U}
    {ℓ : List (DSEntry StmtIn U)} (h : ¬ AnchoredFrom c (e :: ℓ)) :
    ¬ collisionStep e.1 c e.2 ∧ ¬ AnchoredFrom (stepCache c e) ℓ := by
  rw [AnchoredFrom, not_or] at h
  exact h

/-- A fresh forward step that is not an anchored collision yields an answer capacity that is
neither an existing slot nor the query's own capacity. -/
theorem fwd_fresh_cap_new {c : DSCache StmtIn U}
    {a b : CanonicalSpongeState U}
    (hfresh : c.2.find? (fun w => w.1 = a) = none)
    (hnc : ¬ collisionStep (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U).1 c
            (⟨.inr (.inl a), b⟩ : DSEntry StmtIn U).2) :
    b.capacitySegment ∉ slotList c ∧ b.capacitySegment ≠ a.capacitySegment := by
  simp only [collisionStep, hfresh, true_and, not_or] at hnc
  exact hnc

/-- A fresh inverse step that is not an anchored collision yields an answer capacity that is
neither an existing slot nor the query's own capacity. -/
theorem inv_fresh_cap_new {c : DSCache StmtIn U}
    {a b : CanonicalSpongeState U}
    (hfresh : c.2.find? (fun w => w.2 = b) = none)
    (hnc : ¬ collisionStep (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U).1 c
            (⟨.inr (.inr b), a⟩ : DSEntry StmtIn U).2) :
    a.capacitySegment ∉ slotList c ∧ a.capacitySegment ≠ b.capacitySegment := by
  simp only [collisionStep, hfresh, true_and, not_or] at hnc
  exact hnc

/-- A fresh hash step that is not an anchored collision yields an answer that is not an
existing slot. -/
theorem hash_fresh_ans_new {c : DSCache StmtIn U}
    {q : StmtIn} {u : Vector U SpongeSize.C}
    (hfresh : c.1 q = none)
    (hnc : ¬ collisionStep (⟨.inl q, u⟩ : DSEntry StmtIn U).1 c
            (⟨.inl q, u⟩ : DSEntry StmtIn U).2) :
    u ∉ slotList c := by
  simp only [collisionStep, hfresh, true_and] at hnc
  exact hnc

/-! ## Dedup recursion infrastructure (sublist + membership transport) -/

open DuplexSpongeFS.Paper in
/-- The paper dedup output is a sublist of its input (each step erases one entry). -/
theorem removeRedundantEntryDSPaper_sublist
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    (removeRedundantEntryDSPaper log).1.Sublist log := by
  letI : Decidable (∃ idx : Fin log.length,
      DuplexSpongeFS.Paper.redundantEntryDSPaper log idx) := Classical.propDecidable _
  rw [removeRedundantEntryDSPaper]
  by_cases h : ∃ idx : Fin log.length, redundantEntryDSPaper log idx
  · rw [dif_pos h]
    exact (removeRedundantEntryDSPaper_sublist
      (log.eraseIdx (Classical.choose h).val)).trans (List.eraseIdx_sublist _ _)
  · rw [dif_neg h]
termination_by log.length
decreasing_by
  exact (by
    have hlt : (Classical.choose h).val < log.length := (Classical.choose h).isLt
    have heq : (log.eraseIdx (Classical.choose h).val).length + 1 = log.length :=
      List.length_eraseIdx_add_one hlt
    omega)

open DuplexSpongeFS.Paper in
/-- Every entry of the dedup'd base trace was already an entry of the original log. -/
theorem mem_of_mem_removeRedundantEntryDSPaper
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    {e : DSEntry StmtIn U} (he : e ∈ (removeRedundantEntryDSPaper log).1) :
    e ∈ log :=
  (removeRedundantEntryDSPaper_sublist log).subset he

open DuplexSpongeFS.Paper in
/-- A `NoRedundantEntryDSPaper` trace is pairwise class-distinct: no later entry shares a
class with any earlier one. -/
theorem noRedundant_pairwise_classDistinct
    {base : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (h : NoRedundantEntryDSPaper base)
    (i j : Fin base.length) (hij : i < j) :
    ¬ sameClass base[j] base[i] := by
  intro hcl
  exact h j ((redundantEntryDSPaper_iff_sameClass base j).mpr ⟨i, hij, hcl⟩)

open DuplexSpongeFS.Paper in
/-- The dedup output is pairwise class-distinct. -/
theorem removeRedundantEntryDSPaper_pairwise_classDistinct
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (i j : Fin (removeRedundantEntryDSPaper log).1.length) (hij : i < j) :
    ¬ sameClass (removeRedundantEntryDSPaper log).1[j]
        (removeRedundantEntryDSPaper log).1[i] :=
  noRedundant_pairwise_classDistinct (removeRedundantEntryDSPaper log).2 i j hij

/-! ## Slot-list membership of cached capacities -/

/-- Both capacities of a cached permutation pair are slots. -/
theorem mem_slotList_of_mem_perm (c : DSCache StmtIn U)
    {p : CanonicalSpongeState U × CanonicalSpongeState U} (hp : p ∈ c.2) :
    p.1.capacitySegment ∈ slotList c ∧ p.2.capacitySegment ∈ slotList c := by
  classical
  constructor <;>
  · refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨p, hp, ?_⟩)
    simp

/-- A capacity cached early stays a slot of every later fold cache. -/
theorem mem_slotList_foldl_of_mem_perm (c : DSCache StmtIn U)
    (L : List (DSEntry StmtIn U))
    {p : CanonicalSpongeState U × CanonicalSpongeState U} (hp : p ∈ c.2) :
    p.1.capacitySegment ∈ slotList (L.foldl stepCache c) ∧
      p.2.capacitySegment ∈ slotList (L.foldl stepCache c) :=
  mem_slotList_of_mem_perm _ ((foldl_stepCache_perm_sublist c L).subset hp)

/-! ## Assembly: the paper bound conditional on the dedup reduction -/

open DuplexSpongeFS.Paper in
/-- The dedup reduction (the one remaining pure-combinatorics obligation): a log consistent
with the empty cache that satisfies the paper bad event `EPaper` contains an anchored
collision against the empty cache. -/
abbrev EPaperReduction (StmtIn U : Type) [SpongeUnit U] [SpongeSize]
    [DecidableEq StmtIn] [DecidableEq (CanonicalSpongeState U)]
    [Fintype StmtIn] [Fintype U] : Prop :=
  ∀ (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)),
    ConsistentFrom ((∅, []) : DSCache StmtIn U) log →
    EPaper log →
    AnchoredFrom ((∅, []) : DSCache StmtIn U) log

open DuplexSpongeFS.Paper in
/-- **The eager paper bound, conditional on the dedup reduction.** For any `T`-query
adversary, the probability that the logged trace of the eager lazy carrier exhibits
`EPaper`, in real form, is at most `(7T² − 3T)/(2|U|^C)`. -/
theorem probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction
    (hred : EPaperReduction StmtIn U)
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => EPaper z.2 |
        (simulateQ lazyDSImpl ((simulateQ loggingOracle P).run)).run'
          ((∅, ([] : List (CanonicalSpongeState U × CanonicalSpongeState U))))]).toReal
      ≤ DuplexSpongeFS.BirthdayBound.lemma5_8Bound U T := by
  classical
  set Q := (simulateQ loggingOracle P).run with hQ
  have hQbound : IsTotalQueryBound Q T :=
    (OracleComp.isTotalQueryBound_run_simulateQ_loggingOracle_iff P T).mpr hT
  -- Step 1: rewrite the EPaper probability as an EPaper-on-logged-value probability of the
  -- flagged run, via `run'` and the forgetting bridge.
  have heq : Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        EPaper z.2 |
        (simulateQ lazyDSImpl Q).run'
          ((∅, ([] : List (CanonicalSpongeState U × CanonicalSpongeState U))))]
      = Pr[ fun xs : (α × QueryLog (duplexSpongeChallengeOracle StmtIn U))
              × (DSCache StmtIn U × Prop) => EPaper xs.1.2 |
          (simulateQ lazyDSImplFlagged Q).run ((∅, []), False)] := by
    rw [StateT.run'_eq, probEvent_map,
      lazyDSImpl_run_map_flagged Q (∅, []) False, probEvent_map]
    rfl
  rw [heq]
  -- Step 2: monotone step `EPaper xs.1.2 → final flag`, then the engine output.
  refine le_trans (ENNReal.toReal_mono ?_ (probEvent_mono fun xs hxs hEP => ?_))
    (probEvent_flag_final_toReal_le_lemma5_8Bound Q T hQbound)
  · -- the flag probability is finite
    exact ne_of_lt (lt_of_le_of_lt probEvent_le_one ENNReal.one_lt_top)
  · -- the support fact: a consistent EPaper log forces the final flag
    obtain ⟨_, hcons, hflag⟩ := support_flagged_logged P (∅, []) False xs hxs
    rw [hflag]
    exact Or.inr (hred xs.1.2 hcons hEP)

end DuplexSpongeFS.EagerLazyDS

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.lazyDSImplFlagged_step_support
#print axioms DuplexSpongeFS.EagerLazyDS.support_flagged_logged
#print axioms DuplexSpongeFS.EagerLazyDS.redundantEntryDSPaper_iff_sameClass
#print axioms DuplexSpongeFS.EagerLazyDS.mem_slotList_of_mem_perm
#print axioms DuplexSpongeFS.EagerLazyDS.mem_slotList_foldl_of_mem_perm
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_perm_sublist
#print axioms DuplexSpongeFS.EagerLazyDS.stepCache_hash_mono
#print axioms DuplexSpongeFS.EagerLazyDS.foldl_stepCache_perm_sublist
#print axioms DuplexSpongeFS.EagerLazyDS.noRedundant_pairwise_classDistinct
#print axioms DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_pairwise_classDistinct
#print axioms DuplexSpongeFS.EagerLazyDS.hasFwdKey_stepCache_imp
#print axioms DuplexSpongeFS.EagerLazyDS.hasFwdKey_foldl_imp
#print axioms DuplexSpongeFS.EagerLazyDS.hasInvKey_stepCache_imp
#print axioms DuplexSpongeFS.EagerLazyDS.hasInvKey_foldl_imp
#print axioms DuplexSpongeFS.EagerLazyDS.sameClass_of_entryKeys
#print axioms DuplexSpongeFS.EagerLazyDS.mem_imp_sameClass_mem_removeRedundant
#print axioms DuplexSpongeFS.EagerLazyDS.not_anchoredFrom_cons
#print axioms DuplexSpongeFS.EagerLazyDS.fwd_fresh_cap_new
#print axioms DuplexSpongeFS.EagerLazyDS.inv_fresh_cap_new
#print axioms DuplexSpongeFS.EagerLazyDS.hash_fresh_ans_new
#print axioms DuplexSpongeFS.EagerLazyDS.removeRedundantEntryDSPaper_sublist
#print axioms DuplexSpongeFS.EagerLazyDS.mem_of_mem_removeRedundantEntryDSPaper
#print axioms DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction

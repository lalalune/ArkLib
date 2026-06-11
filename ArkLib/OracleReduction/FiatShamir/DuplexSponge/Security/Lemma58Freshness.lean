/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma58CacheProvenance
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.PaperBadEventsEngine

/-!
# Freshness at class-first slots (issue #316, `EPaperReduction` step 2)

On a consistent log, the cache lookup at a class-first slot **misses**: if the key were
cached, provenance supplies an earlier creating entry; consistency forces our entry's answer
to equal the cached one, making our entry equal to the creator (hash / forward) or its
`swapEntry` (inverse creator) — contradicting first-of-class.

Main results:
* `consistentFrom_prefix_getElem` — consistency localizes: entry `k` is consistent with the
  prefix fold;
* `fresh_at_firstOfClass_hash` / `_perm` / `_permInv` — the three freshness cases.

These are exactly the step-2 deliverables of the finishing plan posted on #316; steps 3–4
(the `E_func` vacuity and the `E_dup` → `collisionStep` extraction) consume them together
with the step-1 dedup pullback.
-/

open OracleComp OracleSpec

namespace DuplexSpongeFS.EagerLazyDS

open DuplexSpongeFS.Paper

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn]
  [SampleableType (Vector U SpongeSize.C)]
  [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]
  [Fintype StmtIn] [Fintype U] [DecidableEq U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]

/-- Consistency localizes: on a consistent log, entry `k` is consistent with the cache
folded over the strict prefix before `k`. -/
theorem consistentFrom_prefix_getElem (c₀ : DSCache StmtIn U)
    (log : List (DSEntry StmtIn U)) (h : ConsistentFrom c₀ log)
    (k : ℕ) (hk : k < log.length) :
    entryConsistent ((log.take k).foldl stepCache c₀) log[k] := by
  induction log generalizing c₀ k with
  | nil => exact absurd hk (by simp)
  | cons e ℓ ih =>
      obtain ⟨he, hℓ⟩ := h
      cases k with
      | zero => simpa using he
      | succ k =>
          have hk' : k < ℓ.length := by simpa using hk
          simpa [List.take_succ_cons, List.foldl_cons] using
            ih (stepCache c₀ e) hℓ k hk'

/-- **Freshness (hash case)**: at a class-first slot holding a hash entry, the hash cache
misses. -/
theorem fresh_at_firstOfClass_hash
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    {k : Fin log.length} (hfirst : FirstOfClassAt log k)
    {q : StmtIn} {u : Vector U SpongeSize.C}
    (he : log[k] = ⟨.inl q, u⟩) :
    ((log.take k).foldl stepCache ((∅, []) : DSCache StmtIn U)).1 q = none := by
  by_contra hne
  rcases Option.ne_none_iff_exists'.mp hne with ⟨u', hu'⟩
  -- provenance: the record comes from a prefix entry
  rcases cacheFold_hash_mem _ _ hu' with h0 | hmem
  · simp at h0
  · -- consistency pins our answer to the cached one
    have hc := consistentFrom_prefix_getElem _ _ hcons k k.isLt
    rw [show (log[(k : ℕ)]'k.isLt) = log[k] from rfl, he] at hc
    have hu : u = u' := hc u' hu'
    subst hu
    -- the prefix entry equals ours — contradicting first-of-class
    obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.mp hmem
    have hjlt : j < (k : ℕ) := lt_of_lt_of_le hj (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjlt k.isLt
    have hgetj : log[j]'hjlog = ⟨.inl q, u⟩ := by
      simp only [List.getElem_take] at hjE
      exact hjE
    have := (hfirst ⟨j, hjlog⟩ (by exact_mod_cast hjlt)).1
    exact this (hgetj.trans he.symm)

/-- **Freshness (forward case)**: at a class-first slot holding a forward permutation
entry, the pair cache has no record with that forward key. -/
theorem fresh_at_firstOfClass_perm
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    {k : Fin log.length} (hfirst : FirstOfClassAt log k)
    {sIn b : CanonicalSpongeState U}
    (he : log[k] = ⟨.inr (.inl sIn), b⟩) :
    ((log.take k).foldl stepCache ((∅, []) : DSCache StmtIn U)).2.find?
      (fun w => w.1 = sIn) = none := by
  by_contra hne
  rcases Option.ne_none_iff_exists'.mp hne with ⟨w, hw⟩
  obtain ⟨w1, w2⟩ := w
  have hwmem : (w1, w2) ∈ ((log.take k).foldl stepCache ((∅, []) : DSCache StmtIn U)).2 :=
    List.mem_of_find?_eq_some hw
  have hwkey : w1 = sIn := by
    have := List.find?_some hw
    simpa using this
  subst hwkey
  -- consistency pins our answer to the cached value
  have hc := consistentFrom_prefix_getElem _ _ hcons k k.isLt
  rw [show (log[(k : ℕ)]'k.isLt) = log[k] from rfl, he] at hc
  have hb : b = w2 := hc (w1, w2) hw
  subst hb
  -- provenance: the pair comes from a forward or inverse prefix entry
  rcases cacheFold_pair_mem _ _ hwmem with h0 | hmem | hmem
  · simp at h0
  · -- forward creator: same entry
    obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.mp hmem
    have hjlt : j < (k : ℕ) := lt_of_lt_of_le hj (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjlt k.isLt
    have hfc := hfirst ⟨j, hjlog⟩ (by exact_mod_cast hjlt)
    simp only [List.getElem_take] at hjE
    exact hfc.1 (by show log[j]'hjlog = log[k]; rw [hjE, he])
  · -- inverse creator: the mirror entry
    obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.mp hmem
    have hjlt : j < (k : ℕ) := lt_of_lt_of_le hj (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjlt k.isLt
    have hfc := hfirst ⟨j, hjlog⟩ (by exact_mod_cast hjlt)
    simp only [List.getElem_take] at hjE
    exact hfc.2 (by show log[j]'hjlog = mirrorOf log[k]; rw [hjE, he, Paper.mirrorOf_fwd])

/-- **Freshness (inverse case)**: at a class-first slot holding an inverse permutation
entry, the pair cache has no record with that value key. -/
theorem fresh_at_firstOfClass_permInv
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hcons : ConsistentFrom ((∅, []) : DSCache StmtIn U) log)
    {k : Fin log.length} (hfirst : FirstOfClassAt log k)
    {sOut a : CanonicalSpongeState U}
    (he : log[k] = ⟨.inr (.inr sOut), a⟩) :
    ((log.take k).foldl stepCache ((∅, []) : DSCache StmtIn U)).2.find?
      (fun w => w.2 = sOut) = none := by
  by_contra hne
  rcases Option.ne_none_iff_exists'.mp hne with ⟨w, hw⟩
  obtain ⟨w1, w2⟩ := w
  have hwmem : (w1, w2) ∈ ((log.take k).foldl stepCache ((∅, []) : DSCache StmtIn U)).2 :=
    List.mem_of_find?_eq_some hw
  have hwkey : w2 = sOut := by
    have := List.find?_some hw
    simpa using this
  subst hwkey
  have hc := consistentFrom_prefix_getElem _ _ hcons k k.isLt
  rw [show (log[(k : ℕ)]'k.isLt) = log[k] from rfl, he] at hc
  have ha : a = w1 := hc (w1, w2) hw
  subst ha
  rcases cacheFold_pair_mem _ _ hwmem with h0 | hmem | hmem
  · simp at h0
  · -- forward creator: the mirror entry
    obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.mp hmem
    have hjlt : j < (k : ℕ) := lt_of_lt_of_le hj (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjlt k.isLt
    have hfc := hfirst ⟨j, hjlog⟩ (by exact_mod_cast hjlt)
    simp only [List.getElem_take] at hjE
    exact hfc.2 (by show log[j]'hjlog = mirrorOf log[k]; rw [hjE, he, Paper.mirrorOf_inv])
  · -- inverse creator: same entry
    obtain ⟨j, hj, hjE⟩ := List.mem_iff_getElem.mp hmem
    have hjlt : j < (k : ℕ) := lt_of_lt_of_le hj (by simp [List.length_take])
    have hjlog : j < log.length := lt_trans hjlt k.isLt
    have hfc := hfirst ⟨j, hjlog⟩ (by exact_mod_cast hjlt)
    simp only [List.getElem_take] at hjE
    exact hfc.1 (by show log[j]'hjlog = log[k]; rw [hjE, he])

end DuplexSpongeFS.EagerLazyDS

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.consistentFrom_prefix_getElem
#print axioms DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_hash
#print axioms DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_perm
#print axioms DuplexSpongeFS.EagerLazyDS.fresh_at_firstOfClass_permInv
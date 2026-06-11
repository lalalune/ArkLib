/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma58Freshness

/-!
# Item (v) infrastructure: positional anchoring + certificate-freshness (issue #316)

The three bridge bricks that make the dedup-side disjunct extraction pure per-disjunct
mechanics:

* `swapEntry_eq_mirrorOf` — the Correspondence/Engine vocabulary bridge (the two parallel
  defs on the same sigma agree);
* `firstOfClassAt_of_noRedundant` — the dedup's own `NoRedundantEntryDSPaper` certificate
  gives first-of-class at every index (so the landed `fresh_at_firstOfClass_*` theorems
  apply on the dedup with no pullback);
* `anchoredFrom_of_at` — positional introduction: a `collisionStep` at any single position
  (against the prefix fold) yields `AnchoredFrom`.

With these, item (v) is: per `EPaper` disjunct, the anchor index is fresh (certificate
freshness), the earlier coincidence entry was fresh at ITS index, cached
(`stepCache_caches_fresh_*`), persisted (`foldl_stepCache_*_mono`), its capacity is a slot
(`mem_slotList_of_*`), and the anchor's answer capacity hits it — `collisionStep`, hence
`AnchoredFrom` by `anchoredFrom_of_at`; the `j' = j` cases are `collisionStep`'s self-anchor
disjunct, and `E_func` dies by freshness + pair provenance.
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

/-- The Correspondence-file `swapEntry` and the Engine-file `mirrorOf` are the same map. -/
theorem swapEntry_eq_mirrorOf (e : DSEntry StmtIn U) :
    swapEntry e = Paper.mirrorOf e := by
  rcases e with ⟨t, ans⟩
  rcases t with q | a | b <;> rfl

/-- **Certificate freshness**: the dedup's `NoRedundantEntryDSPaper` certificate gives
first-of-class at every index. -/
theorem firstOfClassAt_of_noRedundant
    {base : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (hnr : Paper.NoRedundantEntryDSPaper base) (j : Fin base.length) :
    Paper.FirstOfClassAt base j := by
  intro j' hj'
  by_contra hcon
  push_neg at hcon
  refine hnr j ((redundantEntryDSPaper_iff_sameClass base j).mpr ⟨j', hj', ?_⟩)
  rcases Classical.em (base[j'] = base[j]) with heq | hne
  · exact Or.inl heq
  · have hmir := hcon (fun h => hne h)
    refine Or.inr ?_
    rw [swapEntry_eq_mirrorOf]
    exact hmir

/-- **Positional anchoring**: a `collisionStep` at any position (against the prefix fold)
yields `AnchoredFrom`. -/
theorem anchoredFrom_of_at (c₀ : DSCache StmtIn U)
    (ℓ : List (DSEntry StmtIn U)) (j : Fin ℓ.length)
    (hcol : collisionStep ℓ[j].1 ((ℓ.take j).foldl stepCache c₀) ℓ[j].2) :
    AnchoredFrom c₀ ℓ := by
  induction ℓ generalizing c₀ with
  | nil => exact j.elim0
  | cons e ℓ' ih =>
      rcases j with ⟨jv, hjv⟩
      cases jv with
      | zero =>
          simp only [List.getElem_cons_zero, List.take_zero, List.foldl_nil] at hcol
          exact Or.inl hcol
      | succ jv =>
          have hjv' : jv < ℓ'.length := by simpa using hjv
          refine Or.inr (ih (stepCache c₀ e) ⟨jv, hjv'⟩ ?_)
          simpa [List.take_succ_cons, List.foldl_cons] using hcol

end DuplexSpongeFS.EagerLazyDS

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.swapEntry_eq_mirrorOf
#print axioms DuplexSpongeFS.EagerLazyDS.firstOfClassAt_of_noRedundant
#print axioms DuplexSpongeFS.EagerLazyDS.anchoredFrom_of_at
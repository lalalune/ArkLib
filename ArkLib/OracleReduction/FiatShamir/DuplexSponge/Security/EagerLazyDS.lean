/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToVCVio.LazyPermBridge
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFoundations

/-!
# The combined lazy duplex-sponge oracle (brick 4C-1)

Toward discharging `Lemma5_8EagerPaperResidual` (CO25 Lemma 5.8): the duplex-sponge
challenge oracle `𝒟_𝔖 = (StmtIn →ₒ Vector U C) + permutationOracle (CanonicalSpongeState U)`
has an eager carrier (`D_DS`: one random hash table, one random permutation) and — defined
here — a **combined lazy implementation** with product state:

* the hash arm is VCVio's per-index caching `randomOracle`;
* the permutation arms are the bidirectional memoizing `lazyPermImpl`
  (`ToVCVio/LazyPermBridge.lean`), consuming the spec via `permutationOracle_eq_sumSpec`.

`dsOverlayFn` is the joint cache overlay (the deterministic answer function obtained by
overlaying both caches on the sampled carrier), the eager side of the combined bridge.
The master product-state induction (brick 4C-2) relates the two.
-/

open OracleComp OracleSpec
open scoped ENNReal NNReal

namespace DuplexSpongeFS.EagerLazyDS

open LazyPermMarginal LazyPermBridge

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn]
  [SampleableType (Vector U SpongeSize.C)]
  [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]
  [Fintype (CanonicalSpongeState U)]

/-- The joint state of the combined lazy oracle: a per-statement hash cache and the
bidirectional permutation cache. -/
abbrev DSCache (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Type :=
  (StmtIn →ₒ Vector U SpongeSize.C).QueryCache ×
    List (CanonicalSpongeState U × CanonicalSpongeState U)

/-- The joint cache overlay: answer hash queries through the hash-cache overlay on the
sampled table, and permutation queries through the permutation-cache overlay on the sampled
permutation. The eager answer function of the combined bridge. -/
def dsOverlayFn (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U)) :
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) →
      (duplexSpongeChallengeOracle StmtIn U).Range t :=
  fun t => match t with
  | .inl s => OracleComp.tableExtending ch g s
  | .inr (.inl sIn) => permExtending cp π sIn
  | .inr (.inr sOut) => (permExtending cp π).symm sOut

/-- The combined lazy implementation: hash queries through the caching `randomOracle`
(threading the hash cache), permutation queries through `lazyPermImpl` (threading the
permutation cache). -/
noncomputable def lazyDSImpl :
    QueryImpl (duplexSpongeChallengeOracle StmtIn U)
      (StateT (DSCache StmtIn U) ProbComp) :=
  fun t s =>
    match t with
    | .inl q =>
        (fun (p : Vector U SpongeSize.C × _) => (p.1, (p.2, s.2))) <$>
          (((StmtIn →ₒ Vector U SpongeSize.C).randomOracle q).run s.1)
    | .inr (.inl sIn) =>
        (fun (p : CanonicalSpongeState U × _) => (p.1, (s.1, p.2))) <$>
          ((lazyPermImpl (.inl sIn :
            CanonicalSpongeState U ⊕ CanonicalSpongeState U)).run s.2)
    | .inr (.inr sOut) =>
        (fun (p : CanonicalSpongeState U × _) => (p.1, (s.1, p.2))) <$>
          ((lazyPermImpl (.inr sOut :
            CanonicalSpongeState U ⊕ CanonicalSpongeState U)).run s.2)

@[simp] lemma dsOverlayFn_inl (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U))
    (s : StmtIn) :
    dsOverlayFn ch cp g π (.inl s) = OracleComp.tableExtending ch g s := rfl

@[simp] lemma dsOverlayFn_fwd (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U))
    (sIn : CanonicalSpongeState U) :
    dsOverlayFn ch cp g π (.inr (.inl sIn)) = permExtending cp π sIn := rfl

@[simp] lemma dsOverlayFn_inv (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U))
    (sOut : CanonicalSpongeState U) :
    dsOverlayFn ch cp g π (.inr (.inr sOut)) = (permExtending cp π).symm sOut := rfl

/-! ## Step facts for the master induction -/

/-- Growing the hash cache at an uncached statement is the table update of the overlay
(the permutation arms are untouched). -/
lemma dsOverlayFn_cacheQuery_of_none
    (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U))
    {q : StmtIn} (hq : ch q = none) (u : Vector U SpongeSize.C) :
    dsOverlayFn (ch.cacheQuery q u) cp g π
      = dsOverlayFn ch cp (Function.update g q u) π := by
  funext t
  rcases t with s | sIn | sOut
  · show OracleComp.tableExtending (ch.cacheQuery q u) g s
      = OracleComp.tableExtending ch (Function.update g q u) s
    rw [OracleComp.tableExtending_cacheQuery, OracleComp.tableExtending_update_of_none ch g hq]
  · rfl
  · rfl

/-- The overlay's hash answer at the queried point recovers the cached/updated value. -/
lemma tableExtending_cacheQuery_self
    (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (g : StmtIn → Vector U SpongeSize.C) (q : StmtIn) (u : Vector U SpongeSize.C) :
    OracleComp.tableExtending (ch.cacheQuery q u) g q = u := by
  simp [OracleComp.tableExtending, OracleSpec.QueryCache.cacheQuery]

/-- Two uniform samples commute under any `ProbComp` continuation: both prefixes are
lifted `PMF`s, so the `OptionT` layer collapses and `PMF.bind_comm` applies. -/
lemma evalDist_uniformSample_swap {β γ : Type} [Fintype β] [Nonempty β] [SampleableType β]
    [Fintype γ] [Nonempty γ] [SampleableType γ] {δ : Type}
    (f : β → γ → ProbComp δ) :
    evalDist (do let b ← $ᵗ β; let c ← $ᵗ γ; f b c)
      = evalDist (do let c ← $ᵗ γ; let b ← $ᵗ β; f b c) := by
  classical
  rw [← SPMF.toPMF_inj]
  rw [evalDist_bind, SPMF.toPMF_bind, evalDist_bind, SPMF.toPMF_bind]
  rw [evalDist_uniformSample, evalDist_uniformSample, SPMF.liftM_eq_map, SPMF.liftM_eq_map,
    SPMF.toPMF_mk, SPMF.toPMF_mk]
  rw [show Option.elimM ((PMF.uniformOfFintype β).map some) (PMF.pure none)
      (fun b => (evalDist ($ᵗ γ >>= fun c => f b c)).toPMF)
    = (PMF.uniformOfFintype β).bind
        (fun b => (evalDist ($ᵗ γ >>= fun c => f b c)).toPMF) from by
    rw [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl]
  rw [show Option.elimM ((PMF.uniformOfFintype γ).map some) (PMF.pure none)
      (fun c => (evalDist ($ᵗ β >>= fun b => f b c)).toPMF)
    = (PMF.uniformOfFintype γ).bind
        (fun c => (evalDist ($ᵗ β >>= fun b => f b c)).toPMF) from by
    rw [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl]
  have hin : ∀ b, (evalDist ($ᵗ γ >>= fun c => f b c)).toPMF
      = (PMF.uniformOfFintype γ).bind (fun c => (evalDist (f b c)).toPMF) := by
    intro b
    rw [evalDist_bind, SPMF.toPMF_bind, evalDist_uniformSample, SPMF.liftM_eq_map,
      SPMF.toPMF_mk, Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl
  have hin' : ∀ c, (evalDist ($ᵗ β >>= fun b => f b c)).toPMF
      = (PMF.uniformOfFintype β).bind (fun b => (evalDist (f b c)).toPMF) := by
    intro c
    rw [evalDist_bind, SPMF.toPMF_bind, evalDist_uniformSample, SPMF.liftM_eq_map,
      SPMF.toPMF_mk, Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl
  simp only [hin, hin']
  exact PMF.bind_comm _ _ _


/-! ## The overlay, factored through its permutation slot -/

/-- The joint overlay as a function of the (already overlaid) permutation: the shape the
spectatored absorptions consume. -/
def dsOverlayOf (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (g : StmtIn → Vector U SpongeSize.C) (σ : Equiv.Perm (CanonicalSpongeState U)) :
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) →
      (duplexSpongeChallengeOracle StmtIn U).Range t :=
  fun t => match t with
  | .inl s => OracleComp.tableExtending ch g s
  | .inr (.inl sIn) => σ sIn
  | .inr (.inr sOut) => σ.symm sOut

lemma dsOverlayFn_eq_overlayOf (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (g : StmtIn → Vector U SpongeSize.C) (π : Equiv.Perm (CanonicalSpongeState U)) :
    dsOverlayFn ch cp g π = dsOverlayOf ch g (LazyPermBridge.permExtending cp π) := by
  funext t
  rcases t with s | sIn | sOut <;> rfl

section TwoSample

variable {β γ : Type} [Fintype β] [Nonempty β] [SampleableType β]
  [Fintype γ] [Nonempty γ] [SampleableType γ]

/-- `toPMF` of a two-sample-then-pure program, as nested PMF binds with the success tag
outermost on the inner fibre. -/
lemma toPMF_two_sample {α : Type} (F : β → γ → α) :
    (evalDist (do
      let b ← $ᵗ β
      let c ← $ᵗ γ
      pure (F b c) : ProbComp α)).toPMF
      = (PMF.uniformOfFintype β).bind
          (fun b => ((PMF.uniformOfFintype γ).map (F b)).map some) := by
  classical
  rw [evalDist_bind, SPMF.toPMF_bind, evalDist_uniformSample, SPMF.liftM_eq_map,
    SPMF.toPMF_mk]
  rw [show Option.elimM ((PMF.uniformOfFintype β).map some) (PMF.pure none)
      (fun b => (evalDist ($ᵗ γ >>= fun c => pure (F b c) : ProbComp α)).toPMF)
    = (PMF.uniformOfFintype β).bind
        (fun b => (evalDist ($ᵗ γ >>= fun c => pure (F b c) : ProbComp α)).toPMF) from by
    rw [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
    rfl]
  refine congrArg _ (funext fun b => ?_)
  have hprog : ($ᵗ γ >>= fun c => pure (F b c) : ProbComp α) = (F b) <$> ($ᵗ γ) := by
    rw [map_eq_bind_pure_comp]
    rfl
  rw [hprog, evalDist_map, SPMF.toPMF_map, evalDist_uniformSample, SPMF.liftM_eq_map,
    SPMF.toPMF_mk, PMF.monad_map_eq_map, PMF.map_comp, PMF.map_comp]
  rfl

end TwoSample

/-! ## The combined master induction -/

section Master

variable [Finite StmtIn]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
  [Nonempty (StmtIn → Vector U SpongeSize.C)]
  [Nonempty (Equiv.Perm (CanonicalSpongeState U))]
  [Fintype (StmtIn → Vector U SpongeSize.C)]
  [Fintype (Vector U SpongeSize.C)] [Nonempty (Vector U SpongeSize.C)]

set_option maxHeartbeats 3200000 in
/-- **The combined eager–lazy duplex-sponge bridge**: simulating against the combined lazy
oracle (caching hash arm, memoizing bidirectional permutation arms) from duplicate-free
caches has the same distribution as sampling one hash table and one permutation and
answering eagerly through the joint cache overlay. -/
theorem evalDist_simulateQ_lazyDSImpl_run'
    {α : Type} (oa : OracleComp (duplexSpongeChallengeOracle StmtIn U) α)
    (ch : (StmtIn →ₒ Vector U SpongeSize.C).QueryCache)
    (cp : List (CanonicalSpongeState U × CanonicalSpongeState U))
    (hkeys : (cp.map Prod.fst).Nodup) (hvals : (cp.map Prod.snd).Nodup) :
    evalDist ((simulateQ lazyDSImpl oa).run' (ch, cp))
      = evalDist (do
          let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
          let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
          pure (evalWithAnswerFn (QueryImpl.ofFn (dsOverlayFn ch cp g π)) oa)
          : ProbComp α) := by
  classical
  induction oa using OracleComp.inductionOn generalizing ch cp with
  | pure a =>
    have hlhs : (simulateQ lazyDSImpl (pure a : OracleComp _ α)).run' (ch, cp)
        = (pure a : ProbComp α) := by
      rw [simulateQ_pure]
      change (fun x => x.1) <$> (pure (a, (ch, cp)) : ProbComp (α × _)) = pure a
      rw [map_pure]
    rw [hlhs]
    simp only [evalWithAnswerFn_pure]
    symm
    refine evalDist_ext fun x => ?_
    rw [probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
      tsum_probOutput_eq_one' (mx := $ᵗ (StmtIn → Vector U SpongeSize.C)) (by simp),
      one_mul, probOutput_bind_eq_tsum, ENNReal.tsum_mul_right,
      tsum_probOutput_eq_one' (mx := $ᵗ (Equiv.Perm (CanonicalSpongeState U))) (by simp),
      one_mul]
  | query_bind t k ih =>
    have hred : (simulateQ lazyDSImpl
          (liftM ((duplexSpongeChallengeOracle StmtIn U).query t) >>= k)).run' (ch, cp)
        = ((lazyDSImpl t).run (ch, cp)) >>= fun p =>
            (simulateQ lazyDSImpl (k p.1)).run' p.2 := by
      rw [simulateQ_bind, simulateQ_spec_query]
      change Prod.fst <$> (((lazyDSImpl t).run (ch, cp)) >>= fun p =>
        (simulateQ lazyDSImpl (k p.1)).run p.2) = _
      rw [map_bind]
      rfl
    have heval : ∀ (f : (t : (duplexSpongeChallengeOracle StmtIn U).Domain) →
          (duplexSpongeChallengeOracle StmtIn U).Range t),
        evalWithAnswerFn (QueryImpl.ofFn f)
            (liftM ((duplexSpongeChallengeOracle StmtIn U).query t) >>= k)
          = evalWithAnswerFn (QueryImpl.ofFn f) (k (f t)) := by
      intro f
      rw [evalWithAnswerFn_bind]
      rfl
    rw [hred]
    simp_rw [heval]
    rcases t with q | sIn | sOut
    · -- hash arm
      have hexpose : (lazyDSImpl
            ((.inl q : (duplexSpongeChallengeOracle StmtIn U).Domain))).run (ch, cp)
          = (fun (p : Vector U SpongeSize.C × _) => (p.1, (p.2, cp))) <$>
              (((StmtIn →ₒ Vector U SpongeSize.C).randomOracle q).run ch) := rfl
      rcases hcq : ch q with _ | u
      · -- hash miss
        rw [hexpose, QueryImpl.withCaching_run_none _ hcq, Functor.map_map]
        rw [show (uniformSampleImpl (spec := (StmtIn →ₒ Vector U SpongeSize.C)) q
            : ProbComp (Vector U SpongeSize.C)) = $ᵗ (Vector U SpongeSize.C) from rfl]
        have hfib : ∀ u : Vector U SpongeSize.C,
            evalDist ((simulateQ lazyDSImpl (k u)).run' (ch.cacheQuery q u, cp))
            = evalDist (do
                let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
                let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
                pure (evalWithAnswerFn
                  (QueryImpl.ofFn (dsOverlayFn ch cp (Function.update g q u) π))
                  (k (Function.update g q u q))) : ProbComp α) := by
          intro u
          rw [ih u (ch.cacheQuery q u) cp hkeys hvals]
          refine congrArg evalDist
            (congrArg (fun F => ($ᵗ _) >>= F) (funext fun g => ?_))
          refine congrArg (fun F => ($ᵗ _) >>= F) (funext fun π => ?_)
          rw [dsOverlayFn_cacheQuery_of_none ch cp g π hcq u]
          exact congrArg (fun z => (pure (evalWithAnswerFn
            (QueryImpl.ofFn (dsOverlayFn ch cp (Function.update g q u) π)) (k z))
              : ProbComp α)) (Function.update_self q u g).symm
        have hassoc : ((((fun a => (a, (ch.cacheQuery q a, cp))) <$>
              ($ᵗ (Vector U SpongeSize.C)))) >>= fun p =>
              (simulateQ lazyDSImpl (k p.1)).run' p.2)
            = (($ᵗ (Vector U SpongeSize.C)) >>= fun a =>
                (simulateQ lazyDSImpl (k a)).run' (ch.cacheQuery q a, cp)) :=
          bind_map_left _ _ _
        refine Eq.trans (congrArg evalDist hassoc) ?_
        rw [evalDist_bind]
        trans (evalDist ($ᵗ (Vector U SpongeSize.C)) >>= fun u =>
          evalDist (do
            let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
            let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
            pure (evalWithAnswerFn
              (QueryImpl.ofFn (dsOverlayFn ch cp (Function.update g q u) π))
              (k (Function.update g q u q))) : ProbComp α))
        · exact congrArg _ (funext fun u => hfib u)
        rw [← evalDist_bind]
        rw [show (($ᵗ (Vector U SpongeSize.C)) >>= fun u => (do
              let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
              let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
              pure (evalWithAnswerFn
                (QueryImpl.ofFn (dsOverlayFn ch cp (Function.update g q u) π))
                (k (Function.update g q u q))) : ProbComp α))
            = ((do
                let u ← $ᵗ (Vector U SpongeSize.C)
                let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
                pure (Function.update g q u)) >>= fun g' => (do
                  let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
                  pure (evalWithAnswerFn (QueryImpl.ofFn (dsOverlayFn ch cp g' π))
                    (k (g' q))) : ProbComp α)) from by
          simp only [bind_assoc, pure_bind]]
        rw [evalDist_bind, evalDist_uniformSample_bind_update q, ← evalDist_bind]
        refine congrArg evalDist
          (congrArg (fun F => ($ᵗ _) >>= F) (funext fun g => ?_))
        refine congrArg (fun F => ($ᵗ _) >>= F) (funext fun π => ?_)
        have : OracleComp.tableExtending ch g q = g q := by
          simp [OracleComp.tableExtending, hcq]
        exact congrArg (fun z => (pure (evalWithAnswerFn
          (QueryImpl.ofFn (dsOverlayFn ch cp g π)) (k z)) : ProbComp α)) this.symm
      · -- hash hit
        rw [hexpose, QueryImpl.withCaching_run_some _ hcq, map_pure]
        have hcollapse : ((pure ((u, ch).1, ((u, ch).2, cp)) : ProbComp _) >>= fun p =>
              (simulateQ lazyDSImpl (k p.1)).run' p.2)
            = (simulateQ lazyDSImpl (k u)).run' (ch, cp) := pure_bind _ _
        refine Eq.trans (congrArg evalDist hcollapse) ?_
        rw [ih u ch cp hkeys hvals]
        refine congrArg evalDist
          (congrArg (fun F => ($ᵗ _) >>= F) (funext fun g => ?_))
        refine congrArg (fun F => ($ᵗ _) >>= F) (funext fun π => ?_)
        have : OracleComp.tableExtending ch g q = u := by
          simp [OracleComp.tableExtending, hcq]
        exact congrArg (fun z => (pure (evalWithAnswerFn
          (QueryImpl.ofFn (dsOverlayFn ch cp g π)) (k z)) : ProbComp α)) this.symm
    · -- forward permutation arm
      have hexpose : (lazyDSImpl ((.inr (.inl sIn) :
            (duplexSpongeChallengeOracle StmtIn U).Domain))).run (ch, cp)
          = (fun (p : CanonicalSpongeState U × _) => (p.1, (ch, p.2))) <$>
              ((LazyPermBridge.lazyPermImpl (.inl sIn :
                CanonicalSpongeState U ⊕ CanonicalSpongeState U)).run cp) := rfl
      rcases hc : cp.find? (fun p => p.1 = sIn) with _ | p
      · -- forward fresh query
        have hfresh : sIn ∉ cp.map Prod.fst := by
          intro hmem
          obtain ⟨w, hw, hw1⟩ := List.mem_map.mp hmem
          have := List.find?_eq_none.mp hc w hw
          simp [hw1] at this
        have hstep := LazyPermBridge.lazyPermImpl_run_inl_none cp hc
        rw [hexpose, hstep, Functor.map_map]
        have hassoc : ((((fun b => ((b, cp.concat (sIn, b)).1,
              (ch, (b, cp.concat (sIn, b)).2))) <$>
              LazyPermBridge.sampleUnused (LazyPermBridge.unusedValuesList cp))) >>= fun p =>
              (simulateQ lazyDSImpl (k p.1)).run' p.2)
            = (LazyPermBridge.sampleUnused (LazyPermBridge.unusedValuesList cp) >>= fun b =>
                (simulateQ lazyDSImpl (k b)).run' (ch, cp.concat (sIn, b))) :=
          bind_map_left _ _ _
        refine Eq.trans (congrArg evalDist hassoc) ?_
        rw [← SPMF.toPMF_inj, evalDist_bind, SPMF.toPMF_bind,
          LazyPermBridge.toPMF_sampleUnused cp sIn hkeys hvals hfresh]
        rw [show Option.elimM ((PMF.uniformOfFinset (LazyPermMarginal.unusedFinset cp)
              (LazyPermMarginal.unusedFinset_nonempty cp sIn hkeys hvals hfresh)).map some)
            (PMF.pure none)
            (fun b => (evalDist ((simulateQ lazyDSImpl (k b)).run'
              (ch, cp.concat (sIn, b)))).toPMF)
          = (PMF.uniformOfFinset (LazyPermMarginal.unusedFinset cp)
              (LazyPermMarginal.unusedFinset_nonempty cp sIn hkeys hvals hfresh)).bind
              (fun b => (evalDist ((simulateQ lazyDSImpl (k b)).run'
                (ch, cp.concat (sIn, b)))).toPMF) from by
          rw [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
          rfl]
        have hfib : ∀ b ∈ (PMF.uniformOfFinset (LazyPermMarginal.unusedFinset cp)
            (LazyPermMarginal.unusedFinset_nonempty cp sIn hkeys hvals hfresh)).support,
            (evalDist ((simulateQ lazyDSImpl (k b)).run' (ch, cp.concat (sIn, b)))).toPMF
            = (PMF.uniformOfFintype (StmtIn → Vector U SpongeSize.C)).bind (fun g =>
                ((PMF.uniformOfFintype (Equiv.Perm (CanonicalSpongeState U))).map
                  (fun π => evalWithAnswerFn
                    (QueryImpl.ofFn (dsOverlayOf ch g
                      (LazyPermBridge.permExtending (cp.concat (sIn, b)) π)))
                    (k (LazyPermBridge.permExtending (cp.concat (sIn, b)) π sIn)))).map
                  some) := by
          intro b hb
          rw [PMF.mem_support_uniformOfFinset_iff, LazyPermMarginal.mem_unusedFinset] at hb
          have hk' : (((cp.concat (sIn, b)).map Prod.fst)).Nodup := by
            simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
            rw [List.nodup_append]
            exact ⟨hkeys, List.nodup_singleton _, by
              intro x hx y hy
              simp only [List.mem_singleton] at hy
              subst hy
              exact fun h => hfresh (h ▸ hx)⟩
          have hv' : (((cp.concat (sIn, b)).map Prod.snd)).Nodup := by
            simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
            rw [List.nodup_append]
            exact ⟨hvals, List.nodup_singleton _, by
              intro x hx y hy
              simp only [List.mem_singleton] at hy
              subst hy
              exact fun h => hb (h ▸ hx)⟩
          rw [ih b ch (cp.concat (sIn, b)) hk' hv', toPMF_two_sample]
          refine congrArg _ (funext fun g => ?_)
          refine congrArg (fun p => PMF.map some p) (congrArg _ (funext fun π => ?_))
          have hagree : LazyPermBridge.permExtending (cp.concat (sIn, b)) π sIn = b := by
            have := LazyPermBridge.extends_permExtending (cp.concat (sIn, b)) π hk' hv'
            exact this (sIn, b) (by simp [List.concat_eq_append])
          dsimp only [Function.comp_apply]
          rw [dsOverlayFn_eq_overlayOf, hagree]
        rw [LazyPermMarginal.bind_congr_support _ _ _ hfib]
        simp only [← PMF.map_bind]
        rw [toPMF_two_sample]
        simp only [dsOverlayFn_eq_overlayOf, dsOverlayFn_fwd]
        simp only [← PMF.map_bind]
        refine congrArg (fun p => PMF.map some p) ?_
        have hne : (LazyPermMarginal.extendsFinset cp).Nonempty := by
          have := LazyPermBridge.extendsFinset_append_nonempty [] cp
            (by simpa using hkeys) (by simpa using hvals) (by simp)
          simpa using this
        exact LazyPermBridge.pmf_absorb_spectator cp sIn hkeys hvals hfresh hne
          (PMF.uniformOfFintype (StmtIn → Vector U SpongeSize.C))
          (fun g σ => evalWithAnswerFn (QueryImpl.ofFn (dsOverlayOf ch g σ)) (k (σ sIn)))
      · -- forward cache hit
        have hp1 : p.1 = sIn := by
          have := List.find?_some hc
          simpa using this
        have hpc : p ∈ cp := List.mem_of_find?_eq_some hc
        have hstep := LazyPermBridge.lazyPermImpl_run_inl_some cp hc
        rw [hexpose, hstep, map_pure]
        have hcollapse : ((pure ((p.2, cp).1, (ch, (p.2, cp).2)) : ProbComp _) >>= fun w =>
              (simulateQ lazyDSImpl (k w.1)).run' w.2)
            = (simulateQ lazyDSImpl (k p.2)).run' (ch, cp) := pure_bind _ _
        refine Eq.trans (congrArg evalDist hcollapse) ?_
        rw [ih p.2 ch cp hkeys hvals]
        refine congrArg evalDist
          (congrArg (fun F => ($ᵗ _) >>= F) (funext fun g => ?_))
        refine congrArg (fun F => ($ᵗ _) >>= F) (funext fun π => ?_)
        have hval : LazyPermBridge.permExtending cp π sIn = p.2 := by
          have := LazyPermBridge.extends_permExtending cp π hkeys hvals p hpc
          rwa [hp1] at this
        exact congrArg (fun z => (pure (evalWithAnswerFn
          (QueryImpl.ofFn (dsOverlayFn ch cp g π)) (k z)) : ProbComp α)) hval.symm
    · -- inverse permutation arm
      have hexpose : (lazyDSImpl ((.inr (.inr sOut) :
            (duplexSpongeChallengeOracle StmtIn U).Domain))).run (ch, cp)
          = (fun (p : CanonicalSpongeState U × _) => (p.1, (ch, p.2))) <$>
              ((LazyPermBridge.lazyPermImpl (.inr sOut :
                CanonicalSpongeState U ⊕ CanonicalSpongeState U)).run cp) := rfl
      rcases hc : cp.find? (fun p => p.2 = sOut) with _ | p
      · -- inverse fresh query
        have hfresh : sOut ∉ cp.map Prod.snd := by
          intro hmem
          obtain ⟨w, hw, hw2⟩ := List.mem_map.mp hmem
          have := List.find?_eq_none.mp hc w hw
          simp [hw2] at this
        have hstep := LazyPermBridge.lazyPermImpl_run_inr_none cp hc
        rw [hexpose, hstep, Functor.map_map]
        have hassoc : ((((fun a => ((a, cp.concat (a, sOut)).1,
              (ch, (a, cp.concat (a, sOut)).2))) <$>
              LazyPermBridge.sampleUnused (LazyPermBridge.unusedKeysList cp))) >>= fun w =>
              (simulateQ lazyDSImpl (k w.1)).run' w.2)
            = (LazyPermBridge.sampleUnused (LazyPermBridge.unusedKeysList cp) >>= fun a =>
                (simulateQ lazyDSImpl (k a)).run' (ch, cp.concat (a, sOut))) :=
          bind_map_left _ _ _
        refine Eq.trans (congrArg evalDist hassoc) ?_
        rw [← SPMF.toPMF_inj, evalDist_bind, SPMF.toPMF_bind,
          LazyPermBridge.toPMF_sampleUnusedKeys cp sOut hkeys hvals hfresh]
        rw [show Option.elimM ((PMF.uniformOfFinset
              (LazyPermMarginal.unusedFinset (cp.map Prod.swap))
              (LazyPermMarginal.unusedFinset_nonempty (cp.map Prod.swap) sOut
                (by simpa [List.map_map, Function.comp_def] using hvals)
                (by simpa [List.map_map, Function.comp_def] using hkeys)
                (by simpa [List.map_map, Function.comp_def] using hfresh))).map some)
            (PMF.pure none)
            (fun a => (evalDist ((simulateQ lazyDSImpl (k a)).run'
              (ch, cp.concat (a, sOut)))).toPMF)
          = (PMF.uniformOfFinset (LazyPermMarginal.unusedFinset (cp.map Prod.swap))
              (LazyPermMarginal.unusedFinset_nonempty (cp.map Prod.swap) sOut
                (by simpa [List.map_map, Function.comp_def] using hvals)
                (by simpa [List.map_map, Function.comp_def] using hkeys)
                (by simpa [List.map_map, Function.comp_def] using hfresh))).bind
              (fun a => (evalDist ((simulateQ lazyDSImpl (k a)).run'
                (ch, cp.concat (a, sOut)))).toPMF) from by
          rw [Option.elimM, PMF.monad_bind_eq_bind, PMF.bind_map]
          rfl]
        have hfib : ∀ a ∈ (PMF.uniformOfFinset
            (LazyPermMarginal.unusedFinset (cp.map Prod.swap))
            (LazyPermMarginal.unusedFinset_nonempty (cp.map Prod.swap) sOut
              (by simpa [List.map_map, Function.comp_def] using hvals)
              (by simpa [List.map_map, Function.comp_def] using hkeys)
              (by simpa [List.map_map, Function.comp_def] using hfresh))).support,
            (evalDist ((simulateQ lazyDSImpl (k a)).run' (ch, cp.concat (a, sOut)))).toPMF
            = (PMF.uniformOfFintype (StmtIn → Vector U SpongeSize.C)).bind (fun g =>
                ((PMF.uniformOfFintype (Equiv.Perm (CanonicalSpongeState U))).map
                  (fun π => evalWithAnswerFn
                    (QueryImpl.ofFn (dsOverlayOf ch g
                      (LazyPermBridge.permExtending (cp.concat (a, sOut)) π)))
                    (k ((LazyPermBridge.permExtending (cp.concat (a, sOut)) π).symm
                      sOut)))).map some) := by
          intro a ha
          rw [PMF.mem_support_uniformOfFinset_iff, LazyPermMarginal.mem_unusedFinset] at ha
          have haK : a ∉ cp.map Prod.fst := by
            simpa [List.map_map, Function.comp_def] using ha
          have hk' : (((cp.concat (a, sOut)).map Prod.fst)).Nodup := by
            simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
            rw [List.nodup_append]
            exact ⟨hkeys, List.nodup_singleton _, by
              intro x hx y hy
              simp only [List.mem_singleton] at hy
              subst hy
              exact fun h => haK (h ▸ hx)⟩
          have hv' : (((cp.concat (a, sOut)).map Prod.snd)).Nodup := by
            simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil]
            rw [List.nodup_append]
            exact ⟨hvals, List.nodup_singleton _, by
              intro x hx y hy
              simp only [List.mem_singleton] at hy
              subst hy
              exact fun h => hfresh (h ▸ hx)⟩
          rw [ih a ch (cp.concat (a, sOut)) hk' hv', toPMF_two_sample]
          refine congrArg _ (funext fun g => ?_)
          refine congrArg (fun p => PMF.map some p) (congrArg _ (funext fun π => ?_))
          have hagree : LazyPermBridge.permExtending (cp.concat (a, sOut)) π a = sOut := by
            have := LazyPermBridge.extends_permExtending (cp.concat (a, sOut)) π hk' hv'
            exact this (a, sOut) (by simp [List.concat_eq_append])
          have hsymm : (LazyPermBridge.permExtending (cp.concat (a, sOut)) π).symm sOut
              = a := (Equiv.symm_apply_eq _).mpr hagree.symm
          dsimp only [Function.comp_apply]
          rw [dsOverlayFn_eq_overlayOf, hsymm]
        rw [LazyPermMarginal.bind_congr_support _ _ _ hfib]
        simp only [← PMF.map_bind]
        rw [toPMF_two_sample]
        simp only [dsOverlayFn_eq_overlayOf, dsOverlayFn_inv]
        simp only [← PMF.map_bind]
        refine congrArg (fun p => PMF.map some p) ?_
        have hne : (LazyPermMarginal.extendsFinset cp).Nonempty := by
          have := LazyPermBridge.extendsFinset_append_nonempty [] cp
            (by simpa using hkeys) (by simpa using hvals) (by simp)
          simpa using this
        exact LazyPermBridge.pmf_absorb_inv_spectator cp sOut hkeys hvals hfresh hne
          (PMF.uniformOfFintype (StmtIn → Vector U SpongeSize.C))
          (fun g σ => evalWithAnswerFn (QueryImpl.ofFn (dsOverlayOf ch g σ)) (k (σ.symm sOut)))
      · -- inverse cache hit
        have hp2 : p.2 = sOut := by
          have := List.find?_some hc
          simpa using this
        have hpc : p ∈ cp := List.mem_of_find?_eq_some hc
        have hstep := LazyPermBridge.lazyPermImpl_run_inr_some cp hc
        rw [hexpose, hstep, map_pure]
        have hcollapse : ((pure ((p.1, cp).1, (ch, (p.1, cp).2)) : ProbComp _) >>= fun w =>
              (simulateQ lazyDSImpl (k w.1)).run' w.2)
            = (simulateQ lazyDSImpl (k p.1)).run' (ch, cp) := pure_bind _ _
        refine Eq.trans (congrArg evalDist hcollapse) ?_
        rw [ih p.1 ch cp hkeys hvals]
        refine congrArg evalDist
          (congrArg (fun F => ($ᵗ _) >>= F) (funext fun g => ?_))
        refine congrArg (fun F => ($ᵗ _) >>= F) (funext fun π => ?_)
        have hval : LazyPermBridge.permExtending cp π p.1 = sOut := by
          have := LazyPermBridge.extends_permExtending cp π hkeys hvals p hpc
          rwa [hp2] at this
        have hsymm : (LazyPermBridge.permExtending cp π).symm sOut = p.1 :=
          (Equiv.symm_apply_eq _).mpr hval.symm
        exact congrArg (fun z => (pure (evalWithAnswerFn
          (QueryImpl.ofFn (dsOverlayFn ch cp g π)) (k z)) : ProbComp α)) hsymm.symm

end Master

/-! ## The connectors (brick 4C-3): the eager `D_DS` game equals the lazy game -/

section Connectors

variable [Fintype U] [DecidableEq U]
variable [Finite StmtIn]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
  [Nonempty (StmtIn → Vector U SpongeSize.C)]
  [Nonempty (Equiv.Perm (CanonicalSpongeState U))]
  [Fintype (StmtIn → Vector U SpongeSize.C)]
  [Fintype (Vector U SpongeSize.C)] [Nonempty (Vector U SpongeSize.C)]

/-- A pure (carrier-determined) implementation simulates to the deterministic evaluation. -/
private lemma simulateQ_pureFn_eq {ι : Type} {spec : OracleSpec ι} {α : Type}
    (f : (t : spec.Domain) → spec.Range t) (P : OracleComp spec α) :
    (simulateQ (fun t => (pure (f t) : ProbComp (spec.Range t))) P : ProbComp α)
      = pure (evalWithAnswerFn (QueryImpl.ofFn f) P) := by
  induction P using OracleComp.inductionOn with
  | pure a => rw [simulateQ_pure, evalWithAnswerFn_pure]
  | query_bind t k ih =>
      rw [simulateQ_bind, evalWithAnswerFn_bind]
      have hq : (simulateQ (fun t => (pure (f t) : ProbComp (spec.Range t)))
            (liftM (spec.query t)) : ProbComp (spec.Range t)) = pure (f t) := by
        simp only [simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query, id_map]
      rw [hq, pure_bind, ih (f t)]
      rfl

/-- The `D_DS` carrier implementation is the joint overlay at empty caches. -/
private lemma dsImpl_eq_overlay (c : (StmtIn → Vector U SpongeSize.C) ×
    Equiv.Perm (CanonicalSpongeState U)) :
    (fun t => ((DuplexSpongeFS.KeyLemmaFoundations.D_DS StmtIn U).toImpl c t
      : ProbComp ((duplexSpongeChallengeOracle StmtIn U).Range t)))
      = (fun t => pure (dsOverlayFn ∅ [] c.1 c.2 t)) := by
  funext t
  rcases t with q | sIn | sOut
  · show (pure (c.1 q) : ProbComp _) = pure (OracleComp.tableExtending ∅ c.1 q)
    rw [OracleComp.tableExtending_empty]
  · show (pure (c.2 sIn) : ProbComp _)
        = pure (LazyPermBridge.permExtending [] c.2 sIn)
    rfl
  · show (pure (c.2.symm sOut) : ProbComp _)
        = pure ((LazyPermBridge.permExtending [] c.2).symm sOut)
    rfl

set_option maxHeartbeats 800000 in
/-- **The `D_DS` eager game equals the combined lazy game (4C-3)**: sampling the duplex
sponge carrier once and answering through it has the distribution of the lazy memoizing
oracle from empty caches. The Lemma 5.8 analysis can therefore run against the lazy side. -/
theorem evalDist_DDS_eq_lazyDSImpl {α : Type}
    (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) :
    evalDist (do
      let c ← (DuplexSpongeFS.KeyLemmaFoundations.D_DS StmtIn U).sample
      simulateQ ((DuplexSpongeFS.KeyLemmaFoundations.D_DS StmtIn U).toImpl c) P)
      = evalDist ((simulateQ lazyDSImpl P).run' (∅, ([] :
          List (CanonicalSpongeState U × CanonicalSpongeState U)))) := by
  classical
  rw [evalDist_simulateQ_lazyDSImpl_run' P ∅ [] (by simp) (by simp)]
  have hsample : ((DuplexSpongeFS.KeyLemmaFoundations.D_DS StmtIn U).sample
      : ProbComp _) = (do
        let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
        let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
        pure (g, π)) := rfl
  have hprog : (do
      let c ← (DuplexSpongeFS.KeyLemmaFoundations.D_DS StmtIn U).sample
      simulateQ ((DuplexSpongeFS.KeyLemmaFoundations.D_DS StmtIn U).toImpl c) P)
      = (do
        let g ← $ᵗ (StmtIn → Vector U SpongeSize.C)
        let π ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
        pure (evalWithAnswerFn (QueryImpl.ofFn (dsOverlayFn ∅ [] g π)) P)) := by
    rw [hsample, bind_assoc]
    refine congrArg (fun F => ($ᵗ _) >>= F) (funext fun g => ?_)
    rw [bind_assoc]
    refine congrArg (fun F => ($ᵗ _) >>= F) (funext fun π => ?_)
    rw [pure_bind]
    have := simulateQ_pureFn_eq (dsOverlayFn ∅ [] g π) P
    rw [show ((DuplexSpongeFS.KeyLemmaFoundations.D_DS StmtIn U).toImpl (g, π)
        : QueryImpl _ ProbComp) = (fun t => pure (dsOverlayFn ∅ [] g π t)) from
      dsImpl_eq_overlay (g, π)]
    exact this
  rw [hprog]

/-- Events transport through the bridge: any predicate's probability under the eager
`D_DS` game equals its probability under the lazy game. The Lemma 5.8 accounting can
therefore be performed entirely on the lazy side. -/
theorem probEvent_DDS_eq_lazyDSImpl {α : Type}
    (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (p : α → Prop) :
    Pr[ p | do
      let c ← (DuplexSpongeFS.KeyLemmaFoundations.D_DS StmtIn U).sample
      simulateQ ((DuplexSpongeFS.KeyLemmaFoundations.D_DS StmtIn U).toImpl c) P]
      = Pr[ p | (simulateQ lazyDSImpl P).run' (∅, ([] :
          List (CanonicalSpongeState U × CanonicalSpongeState U)))] := by
  unfold probEvent
  rw [evalDist_DDS_eq_lazyDSImpl]

end Connectors

end DuplexSpongeFS.EagerLazyDS
/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.evalDist_uniformSample_swap
#print axioms DuplexSpongeFS.EagerLazyDS.dsOverlayFn_cacheQuery_of_none
#print axioms DuplexSpongeFS.EagerLazyDS.toPMF_two_sample
#print axioms DuplexSpongeFS.EagerLazyDS.evalDist_simulateQ_lazyDSImpl_run'
#print axioms DuplexSpongeFS.EagerLazyDS.evalDist_DDS_eq_lazyDSImpl
#print axioms DuplexSpongeFS.EagerLazyDS.probEvent_DDS_eq_lazyDSImpl

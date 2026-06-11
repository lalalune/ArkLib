/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToVCVio.LazyPermMarginal
import VCVio

/-!
# The lazy permutation oracle — implementations and step distributions

Brick 4 (increment A) of the eager–lazy permutation bridge behind CO25 Lemma 5.8
(`Lemma5_8EagerPaperResidual`): the two implementations of a bidirectional permutation
oracle `(X ⊕ X) →ₒ X` (forward queries on `.inl`, inverse queries on `.inr`), and the
distribution facts for a single lazy step.

* `eagerPermImpl π` — answer through a fixed permutation (the once-sampled carrier);
* `lazyPermImpl` — memoize a growing cache of pairs; answer cache hits deterministically
  and fresh queries by a uniform draw from the unused side (`sampleUnused`, with a junk
  default for the unreachable empty case);
* `evalDist_sampleUnused` — over a duplicate-free nonempty list, `sampleUnused` is the
  uniform distribution on the list's finset, connecting the implementation to the
  chain-rule lemmas of `LazyPermMarginal`.

The master `simulateQ` induction (lazy from a realizable cache ≡ draw a uniform extension
once, then answer eagerly) is increment B.
-/

open OracleComp OracleSpec
open scoped ENNReal NNReal

namespace LazyPermBridge

open LazyPermMarginal

variable {X : Type} [DecidableEq X] [Inhabited X]

/-- Answer both directions of the permutation oracle through a fixed permutation. -/
noncomputable def eagerPermImpl (π : Equiv.Perm X) :
    QueryImpl ((X ⊕ X) →ₒ X) ProbComp :=
  fun t => pure (match t with
    | .inl a => π a
    | .inr b => π.symm b)

/-- Uniformly sample an element of a list (junk default on the empty list, which is
unreachable from realizable caches). -/
noncomputable def sampleUnused (xs : List X) : ProbComp X :=
  match xs with
  | [] => pure default
  | y :: ys => ((y :: ys)[·]) <$> $[0..ys.length]

variable [Fintype X]

/-- The unused outputs of a cache, as a list (for sampling). -/
noncomputable def unusedValuesList (c : List (X × X)) : List X := by
  classical
  exact (Finset.univ.filter (fun b : X => b ∉ c.map Prod.snd)).toList

/-- The unused inputs of a cache, as a list (for sampling on inverse queries). -/
noncomputable def unusedKeysList (c : List (X × X)) : List X := by
  classical
  exact (Finset.univ.filter (fun a : X => a ∉ c.map Prod.fst)).toList

/-- The lazy bidirectional permutation oracle: cache hits answer deterministically; fresh
queries draw uniformly from the unused side and record the new pair. -/
noncomputable def lazyPermImpl :
    QueryImpl ((X ⊕ X) →ₒ X) (StateT (List (X × X)) ProbComp) :=
  fun t c =>
    match t with
    | .inl a =>
        match c.find? (fun p => p.1 = a) with
        | some p => pure (p.2, c)
        | none => (fun b => (b, c.concat (a, b))) <$> sampleUnused (unusedValuesList c)
    | .inr b =>
        match c.find? (fun p => p.2 = b) with
        | some p => pure (p.1, c)
        | none => (fun a => (a, c.concat (a, b))) <$> sampleUnused (unusedKeysList c)

section Facts

@[simp] lemma mem_unusedValuesList {c : List (X × X)} {b : X} :
    b ∈ unusedValuesList c ↔ b ∉ c.map Prod.snd := by
  classical
  simp [unusedValuesList]

@[simp] lemma mem_unusedKeysList {c : List (X × X)} {a : X} :
    a ∈ unusedKeysList c ↔ a ∉ c.map Prod.fst := by
  classical
  simp [unusedKeysList]

lemma unusedValuesList_nodup (c : List (X × X)) : (unusedValuesList c).Nodup := by
  classical
  exact Finset.nodup_toList _

lemma unusedKeysList_nodup (c : List (X × X)) : (unusedKeysList c).Nodup := by
  classical
  exact Finset.nodup_toList _

/-- **The lazy step distribution**: over a duplicate-free nonempty list, `sampleUnused` is
the uniform distribution on the list's finset (lifted to the success branch). This connects
the implementation's fresh-query step to the chain rules of `LazyPermMarginal`. -/
theorem evalDist_sampleUnused_run (xs : List X) (hnd : xs.Nodup) (hxs : xs ≠ []) :
    (evalDist (sampleUnused xs)).run
      = (PMF.uniformOfFinset xs.toFinset (by
          simpa [Finset.nonempty_iff_ne_empty, List.toFinset_eq_empty_iff] using hxs)).map
            some := by
  classical
  rcases xs with _ | ⟨y, ys⟩
  · exact absurd rfl hxs
  · ext o
    rcases o with _ | x
    · -- failure mass is zero on both sides
      have hfail : Pr[⊥ | sampleUnused (y :: ys)] = 0 := by
        simp [sampleUnused]
      rw [show ((evalDist (sampleUnused (y :: ys))).run none)
          = Pr[⊥ | sampleUnused (y :: ys)] from rfl, hfail]
      rw [PMF.map_apply]
      refine (ENNReal.tsum_eq_zero.mpr fun b => ?_).symm
      simp
    · -- success mass: `count/length = 1/card` for a duplicate-free list
      have hout : ((evalDist (sampleUnused (y :: ys))).run (some x))
          = Pr[= x | sampleUnused (y :: ys)] := rfl
      rw [hout]
      have hcount : Pr[= x | sampleUnused (y :: ys)]
          = ((y :: ys).count x : ℝ≥0∞) / (y :: ys).length := by
        show Pr[= x | ((y :: ys)[·]) <$> $[0..ys.length]] = _
        rw [List.count, ← List.countP_eq_sum_fin_ite]
        simp [probOutput_map_eq_sum_fintype_ite, div_eq_mul_inv, @eq_comm _ x]
      rw [hcount, PMF.map_apply]
      refine Eq.trans ?_ (tsum_eq_single x
        (fun b hb => if_neg (fun h => hb (Option.some_inj.mp h).symm))).symm
      rw [if_pos rfl]
      by_cases hx : x ∈ (y :: ys)
      · rw [PMF.uniformOfFinset_apply_of_mem (hs := ⟨y, by simp⟩)
            (List.mem_toFinset.mpr hx),
          List.count_eq_one_of_mem hnd hx, List.toFinset_card_of_nodup hnd]
        simp [ENNReal.div_eq_inv_mul]
      · rw [PMF.uniformOfFinset_apply_of_notMem (hs := ⟨y, by simp⟩)
            (fun h => hx (List.mem_toFinset.mp h)),
          List.count_eq_zero_of_not_mem hx]
        simp


/-! ## The permutation overlay (`tableExtending` analogue)

`permExtending c π` corrects `π` to agree with every cached pair by **pre-composition**
swaps, processed left to right: fixing `(a, b)` disturbs only the inputs `a` and `π⁻¹ b`,
so (for a duplicate-free cache) earlier corrections are never undone. -/

/-- Overlay a cache on a permutation: pre-composition swap corrections force agreement
with every cached pair. -/
def permExtending (c : List (X × X)) (π : Equiv.Perm X) : Equiv.Perm X :=
  c.foldl (fun π' p => (Equiv.swap p.1 (π'.symm p.2)).trans π') π

@[simp] lemma permExtending_nil (π : Equiv.Perm X) : permExtending [] π = π := rfl

lemma permExtending_cons (p : X × X) (c : List (X × X)) (π : Equiv.Perm X) :
    permExtending (p :: c) π
      = permExtending c ((Equiv.swap p.1 (π.symm p.2)).trans π) := rfl

/-- The one-pair correction sends `a` to `b`. -/
lemma onestep_apply_self (a b : X) (π : Equiv.Perm X) :
    ((Equiv.swap a (π.symm b)).trans π) a = b := by
  simp [Equiv.trans_apply, Equiv.swap_apply_left]

/-- The one-pair correction fixes any input other than `a` whose value is not `b`. -/
lemma onestep_apply_of_ne (a b x : X) (π : Equiv.Perm X)
    (hxa : x ≠ a) (hxb : π x ≠ b) :
    ((Equiv.swap a (π.symm b)).trans π) x = π x := by
  rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne hxa]
  intro h
  exact hxb (by rw [h, Equiv.apply_symm_apply])

/-- **Overlay preservation**: a pair already realized by `π` and disjoint from the cache
keys and values survives the overlay. -/
lemma permExtending_preserves (c : List (X × X)) (π : Equiv.Perm X) {a b : X}
    (ha : a ∉ c.map Prod.fst) (hb : b ∉ c.map Prod.snd) (hab : π a = b) :
    permExtending c π a = b := by
  induction c generalizing π with
  | nil => simpa using hab
  | cons p rest ih =>
      rw [permExtending_cons]
      have hpa : a ≠ p.1 := fun h => ha (by simp [h])
      have hpb : π a ≠ p.2 := by
        rw [hab]
        exact fun h => hb (by simp [h])
      exact ih _ (fun h => ha (List.mem_cons_of_mem _ h))
        (fun h => hb (List.mem_cons_of_mem _ h))
        (by rw [onestep_apply_of_ne p.1 p.2 a π hpa hpb, hab])

/-- **Overlay agreement**: the overlay realizes every cached pair (duplicate-free cache). -/
lemma extends_permExtending (c : List (X × X)) (π : Equiv.Perm X)
    (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup) :
    Extends (permExtending c π) c := by
  induction c generalizing π with
  | nil => exact extends_nil _
  | cons p rest ih =>
      intro q hq
      rw [permExtending_cons]
      rcases List.mem_cons.mp hq with rfl | hq
      · -- the head pair: established by its own correction, preserved by the rest
        refine permExtending_preserves rest _ ?_ ?_ (onestep_apply_self q.1 q.2 π)
        · exact fun h => (List.nodup_cons.mp (by simpa using hkeys)).1 h
        · exact fun h => (List.nodup_cons.mp (by simpa using hvals)).1 h
      · exact ih _ ((List.nodup_cons.mp (by simpa using hkeys)).2)
          ((List.nodup_cons.mp (by simpa using hvals)).2) q hq

/-! ## The master eager–lazy induction -/

/-- The unused-values list enumerates the unused finset. -/
lemma toFinset_unusedValuesList (c : List (X × X)) :
    (unusedValuesList c).toFinset = unusedFinset c := by
  classical
  ext b
  simp [unusedValuesList, unusedFinset]

/-- The unused-keys list enumerates the swapped cache's unused finset. -/
lemma toFinset_unusedKeysList (c : List (X × X)) :
    (unusedKeysList c).toFinset = unusedFinset (c.map Prod.swap) := by
  classical
  ext a
  simp [unusedKeysList, unusedFinset, List.map_map, Function.comp_def]

/-- `bind` of a PMF against an `Option.elim`-shaped function only depends on the success
branch over the success support. -/
private lemma pmf_bind_elim_congr {α β : Type} (p : PMF (Option α))
    (f g : α → PMF (Option β))
    (h : ∀ a, p (some a) ≠ 0 → f a = g a) :
    (p.bind (fun o => o.elim (PMF.pure none) f))
      = (p.bind (fun o => o.elim (PMF.pure none) g)) := by
  classical
  ext b
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun o => ?_
  rcases o with _ | a
  · rfl
  · rcases eq_or_ne (p (some a)) 0 with ha | ha
    · rw [ha, zero_mul, zero_mul]
    · simp only [Option.elim_some]
      rw [h a ha]

/- WIP (4B master induction — design in memory; statement+pure case verified in-session):
/-- **The eager–lazy permutation bridge**: simulating against the lazy memoizing oracle
from a realizable cache has the same distribution as drawing one uniform extension of the
cache and answering eagerly through it. Induction on the computation; cache hits are
deterministic on both sides, and fresh queries are exactly the chain rules of
`LazyPermMarginal`. -/
theorem evalDist_simulateQ_lazyPermImpl_run'
    {α : Type} (oa : OracleComp ((X ⊕ X) →ₒ X) α)
    (c : List (X × X)) (hkeys : (c.map Prod.fst).Nodup) (hvals : (c.map Prod.snd).Nodup)
    (hne : (extendsFinset c).Nonempty) :
    (evalDist ((simulateQ lazyPermImpl oa).run' c)).run
      = (PMF.uniformOfFinset (extendsFinset c) hne).bind
          (fun π => (evalDist (simulateQ (eagerPermImpl π) oa)).run) := by
  classical
  induction oa using OracleComp.inductionOn generalizing c with
  | pure a =>
      simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure]
      refine Eq.symm (PMF.bind_const _ _)
  | query_bind t oa ih =>
      sorry

-/

end Facts

end LazyPermBridge

/-! ## Axiom audit — kernel-clean. -/
#print axioms LazyPermBridge.evalDist_sampleUnused_run

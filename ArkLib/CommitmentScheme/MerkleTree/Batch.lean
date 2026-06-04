/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import VCVio

/-!
# Batch openings and batch-index completeness for inductive Merkle trees

This file extends the VCVio inductive Merkle tree
(`VCVio.CryptoFoundations.MerkleTree.Inductive`) with **batch openings** — opening a finite list of
leaf indices at once — and proves **batch-index completeness**: an honestly produced batch of
openings all verify against the honest root.

## Design note: a *non-vacuous* completeness statement

The single-index completeness theorem shipped in VCVio is phrased as `NeverFail` of the *run* of an
`OptionT (OracleComp ...)` computation. That phrasing turns out to be **vacuous with respect to
verification success**: `OptionT.run` reifies a `guard` rejection as the ordinary value `none`, and
a total `ProbComp` always *produces* `none` without *failing*; so `NeverFail (… .run)` holds even
for openings that are rejected. (See `simulateQ_verifyProof_rejects_wrong_root` for the certificate
that rejection is observable, hence the statements here are not vacuous.)

We therefore state completeness as an explicit *acceptance* equality: simulating the verifier over a
deterministic hash oracle `f` returns `some ()` (accept), and never `none` (reject). The connector
`simulateQ_verifyProof_run` reduces the monadic verifier to the functional acceptance predicate, and
everything else is built on top of the VCVio functional `functional_completeness`.

## Main results

* `simulateQ_verifyProof_run` — the verifier, simulated over a deterministic oracle, accepts iff the
  recomputed putative root equals the claimed root.
* `simulateQ_honest_verify_accepts` — single-index completeness, acceptance form.
* `functional_batch_completeness` — every honest opening in a batch reconstructs the root.
* `simulateQ_honest_batch_verify_accepts` — every honest opening in a batch verifies (accept).
* `simulateQ_honest_batch_run_accepts` — the whole batch, verified in one `mapM` pass, accepts.
-/

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type _}

theorem simulateQ_verifyProof_run [DecidableEq α] {s : Skeleton}
    (idx : SkeletonLeafIndex s) (leafValue rootValue : α)
    (proof : List.Vector α idx.depth)
    (f : QueryImpl (spec α) Id) :
    (simulateQ f (verifyProof (m := OracleComp (spec α)) idx leafValue rootValue proof).run)
      = (if getPutativeRootWithHash idx leafValue proof (fun l r => f ⟨l, r⟩) = rootValue
          then some () else none : Id (Option Unit)) := by
  unfold verifyProof
  rw [simulateQ_optionT_bind']
  rw [show (liftM (getPutativeRoot idx leafValue proof) : OptionT (OracleComp (spec α)) α).run
        = (Functor.map some (getPutativeRoot idx leafValue proof)) from rfl]
  rw [simulateQ_map, simulateQ_getPutativeRoot]
  simp only [Functor.map, OracleComp.guard_eq, OptionT.run]
  generalize hg : (getPutativeRootWithHash idx leafValue proof fun l r => f (l, r)) = g
  simp only [OptionT.bind, OptionT.mk, bind]
  by_cases h : g = rootValue
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]; rfl

/-- **Non-vacuity of the completeness statements.** Verification against a root that does *not*
match the recomputed putative root is *rejected* (returns `none`), not accepted. This certifies
that the `= some ()` form of the completeness theorems below has genuine content: it is not the
case that the run accepts unconditionally. (Contrast with the `NeverFail`-of-`.run` form, which
is vacuous because `OptionT.run` reifies a `guard` rejection as the ordinary value `none`,
which a total `ProbComp` never *fails* to produce.) -/
theorem simulateQ_verifyProof_rejects_wrong_root [DecidableEq α] {s : Skeleton}
    (idx : SkeletonLeafIndex s) (leafValue wrongRoot : α)
    (proof : List.Vector α idx.depth) (f : QueryImpl (spec α) Id)
    (hne : getPutativeRootWithHash idx leafValue proof (fun l r => f ⟨l, r⟩) ≠ wrongRoot) :
    (simulateQ f (verifyProof (m := OracleComp (spec α)) idx leafValue wrongRoot proof).run)
      = (none : Id (Option Unit)) := by
  rw [simulateQ_verifyProof_run, if_neg hne]

/-- Honest single-index verification accepts (returns `some ()`) over any deterministic
hash oracle `f`: building the tree, generating the proof, and verifying it always succeeds. -/
theorem simulateQ_honest_verify_accepts [DecidableEq α] {s : Skeleton}
    (leaf_data_tree : LeafData α s) (idx : SkeletonLeafIndex s)
    (f : QueryImpl (spec α) Id) :
    (simulateQ f (do
      let cache ← (buildMerkleTree leaf_data_tree : OracleComp (spec α) _)
      (verifyProof (m := OracleComp (spec α)) idx (leaf_data_tree.get idx)
        (cache.getRootValue) (generateProof cache idx)).run)) = (some () : Id (Option Unit)) := by
  rw [simulateQ_bind, simulateQ_buildMerkleTree]
  show simulateQ f (verifyProof idx (leaf_data_tree.get idx)
    (buildMerkleTreeWithHash leaf_data_tree (fun l r => f ⟨l, r⟩)).getRootValue
    (generateProof (buildMerkleTreeWithHash leaf_data_tree (fun l r => f ⟨l, r⟩)) idx)).run = some ()
  rw [simulateQ_verifyProof_run, if_pos]
  exact functional_completeness idx leaf_data_tree (fun l r => f ⟨l, r⟩)

/-- A batch opening for a list of requested leaf indices. Each entry packages the index,
the claimed leaf value (read off the data tree), and the single-index authentication path. -/
def batchOpening {s : Skeleton} (leaf_data_tree : LeafData α s) (cache : FullData α s)
    (idxs : List (SkeletonLeafIndex s)) :
    List ((i : SkeletonLeafIndex s) × α × List.Vector α i.depth) :=
  idxs.map (fun i => ⟨i, leaf_data_tree.get i, generateProof cache i⟩)

/-- Verify one packaged opening against a claimed root, in `OptionT (OracleComp ...)`. -/
def verifyOpening [DecidableEq α] {s : Skeleton}
    (rootValue : α) (o : (i : SkeletonLeafIndex s) × α × List.Vector α i.depth) :
    OptionT (OracleComp (spec α)) Unit :=
  verifyProof (m := OracleComp (spec α)) o.1 o.2.1 rootValue o.2.2

/-- `composeBuild` (the binary-tree builder) and `buildMerkleTreeWithHash` produce the same
full tree for a given hash function. -/
theorem composeBuild_eq_buildMerkleTreeWithHash {s : Skeleton}
    (leaf_data_tree : LeafData α s) (hash : α → α → α) :
    LeafData.composeBuild leaf_data_tree hash
      = buildMerkleTreeWithHash leaf_data_tree hash := by
  induction leaf_data_tree with
  | leaf a => rfl
  | internal leftData rightData ihl ihr =>
    rw [LeafData.composeBuild, buildMerkleTreeWithHash, ihl, ihr]

/-- Functional batch completeness: every honest opening in the batch reconstructs the root.
This follows from the single-index `functional_completeness` by `List.map`/membership. -/
theorem functional_batch_completeness {s : Skeleton}
    (idxs : List (SkeletonLeafIndex s)) (leaf_data_tree : LeafData α s) (hash : α → α → α) :
    ∀ o ∈ batchOpening leaf_data_tree
        (LeafData.composeBuild leaf_data_tree hash) idxs,
      getPutativeRootWithHash o.1 o.2.1 o.2.2 hash =
      (LeafData.composeBuild leaf_data_tree hash).getRootValue := by
  intro o ho
  simp only [batchOpening, List.mem_map] at ho
  obtain ⟨i, _, rfl⟩ := ho
  rw [composeBuild_eq_buildMerkleTreeWithHash]
  exact functional_completeness i leaf_data_tree hash

/-- Single packaged-opening completeness over a deterministic oracle: an honest opening
(its index, the true leaf value, and the honest path) verifies against the honest root. -/
theorem simulateQ_verifyOpening_honest [DecidableEq α] {s : Skeleton}
    (leaf_data_tree : LeafData α s) (idx : SkeletonLeafIndex s)
    (f : QueryImpl (spec α) Id) :
    (simulateQ f (verifyOpening
      (buildMerkleTreeWithHash leaf_data_tree (fun l r => f ⟨l, r⟩)).getRootValue
      ⟨idx, leaf_data_tree.get idx,
        generateProof (buildMerkleTreeWithHash leaf_data_tree (fun l r => f ⟨l, r⟩)) idx⟩).run)
      = (some () : Id (Option Unit)) := by
  unfold verifyOpening
  rw [simulateQ_verifyProof_run, if_pos]
  exact functional_completeness idx leaf_data_tree (fun l r => f ⟨l, r⟩)

/-- **Batch-index completeness** over a deterministic oracle: every honest opening in a batch
verifies. For any requested list of indices, building the tree once and verifying each requested
opening against the honest root accepts (returns `some ()`) — for *every* opening in the batch.

This is the batch analogue of `simulateQ_honest_verify_accepts`, established from the
single-opening completeness `simulateQ_verifyOpening_honest` via membership in the batch. -/
theorem simulateQ_honest_batch_verify_accepts [DecidableEq α] {s : Skeleton}
    (leaf_data_tree : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (f : QueryImpl (spec α) Id) :
    ∀ o ∈ batchOpening leaf_data_tree
        (buildMerkleTreeWithHash leaf_data_tree (fun l r => f ⟨l, r⟩)) idxs,
      (simulateQ f (verifyOpening
        (buildMerkleTreeWithHash leaf_data_tree (fun l r => f ⟨l, r⟩)).getRootValue o).run)
        = (some () : Id (Option Unit)) := by
  intro o ho
  simp only [batchOpening, List.mem_map] at ho
  obtain ⟨i, _, rfl⟩ := ho
  exact simulateQ_verifyOpening_honest leaf_data_tree i f

/-- Generic helper: if every element of a list verifies (returns `some ()`) under the
deterministic oracle `f`, then verifying the whole list with `List.mapM` accepts, returning
`some (replicate n ())`. -/
theorem simulateQ_mapM_all_accept [DecidableEq α]
    (f : QueryImpl (spec α) Id) {β : Type}
    (g : β → OptionT (OracleComp (spec α)) Unit) (os : List β)
    (h : ∀ o ∈ os, simulateQ f (g o).run = (some () : Id (Option Unit))) :
    simulateQ f (os.mapM g).run
      = (some (List.replicate os.length ()) : Id (Option (List Unit))) := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    rw [List.mapM_cons, simulateQ_optionT_bind', h o (by simp)]
    show simulateQ f ((os.mapM g >>= fun lift => pure (() :: lift)).run)
      = some (List.replicate (o :: os).length ())
    rw [simulateQ_optionT_bind', ih (fun o' ho' => h o' (by simp [ho']))]
    rfl

/-- **Whole-batch run completeness** over a deterministic oracle: building the tree once and
verifying *all* requested openings in a single `mapM` pass accepts — the run returns
`some (replicate idxs.length ())`, i.e. no opening is rejected.

This is the strongest batch-index completeness statement: it is honestly non-vacuous (a single
`guard` rejection anywhere would make the run return `none`), and it reduces to
`simulateQ_honest_batch_verify_accepts` via the `mapM` helper. -/
theorem simulateQ_honest_batch_run_accepts [DecidableEq α] {s : Skeleton}
    (leaf_data_tree : LeafData α s) (idxs : List (SkeletonLeafIndex s))
    (f : QueryImpl (spec α) Id) :
    (simulateQ f (do
      let cache ← (buildMerkleTree leaf_data_tree : OracleComp (spec α) _)
      ((batchOpening leaf_data_tree cache idxs).mapM
        (fun o => verifyOpening cache.getRootValue o)).run))
      = (some (List.replicate idxs.length ()) : Id (Option (List Unit))) := by
  rw [simulateQ_bind, simulateQ_buildMerkleTree]
  show simulateQ f
      (((batchOpening leaf_data_tree
        (buildMerkleTreeWithHash leaf_data_tree (fun l r => f ⟨l, r⟩)) idxs).mapM
        (fun o => verifyOpening
          (buildMerkleTreeWithHash leaf_data_tree (fun l r => f ⟨l, r⟩)).getRootValue o)).run)
      = some (List.replicate idxs.length ())
  rw [simulateQ_mapM_all_accept f _ _
    (simulateQ_honest_batch_verify_accepts leaf_data_tree idxs f)]
  simp only [batchOpening, List.length_map]

end InductiveMerkleTree

/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.CommitmentScheme.MerkleTree.Extraction
import VCVio

/-!
# Hiding for inductive Merkle-tree commitments (salted leaves)

A plain Merkle commitment is *not* hiding: the root and an opening can leak information about the
committed leaf (e.g. a low-entropy leaf can be brute-forced through the public hash). The standard
fix (SNARGs book §18) is to commit to *salted* leaves: each leaf `v` is replaced by a leaf
commitment `leafCommit r v` using fresh randomness (salt) `r`, and the Merkle tree is built over the
salted leaves. Opening reveals `(v, r)` together with the authentication path.

This file provides:

* `leafCommit` / `saltedLeaves` / `buildSaltedTree` — the salted-leaf commitment construction over
  the VCVio inductive Merkle tree.
* `salted_completeness` — a **fully proven** correctness lemma: the salted construction is itself an
  honest Merkle tree over the commitment leaves, so single-index completeness transports verbatim.
* `Hiding` — the **definition** of the hiding security property in the indistinguishability style
  (SNARGs book §18): the joint distribution of `(root, openings)` for any two leaf assignments that
  agree on the *opened* positions are computationally indistinguishable. This is stated as a `Prop`
  over distributions; it is *not* proven here, because establishing it requires a random-oracle /
  computational-indistinguishability argument over the salt distribution (see the roadmap below).

## Roadmap for a full hiding proof (not attempted here — research-grade)

A simulation-based hiding proof needs: (1) a simulator that produces `(root, openings)` from only
the opened leaves and the public parameters, sampling the unopened salted leaves uniformly; and
(2) a hybrid argument over the random oracle showing the simulated and real transcripts are
statistically/computationally close, using that each unopened salted leaf `leafCommit r v` is
(near-)uniform when `r` is fresh. Neither ingredient is available as a finished VCVio lemma, so we
record the property as a definition and keep the construction-level correctness fully proven.
-/

namespace InductiveMerkleTree

open List OracleSpec OracleComp BinaryTree

variable {α : Type _}

/-- A salted leaf commitment: combine a leaf value `v` with salt `r` via the compression function.
Using the same two-to-one `hashFn` keeps the construction inside the single-oracle model. -/
def leafCommit (hashFn : α → α → α) (r v : α) : α := hashFn r v

/-- Replace every leaf `v` of the data tree by its salted commitment, given a salt tree `salts`
of the same shape. -/
def saltedLeaves {s : Skeleton} (hashFn : α → α → α)
    (salts : LeafData α s) (leaves : LeafData α s) : LeafData α s :=
  match salts, leaves with
  | LeafData.leaf r, LeafData.leaf v => LeafData.leaf (leafCommit hashFn r v)
  | LeafData.internal sl sr, LeafData.internal ll lr =>
    LeafData.internal (saltedLeaves hashFn sl ll) (saltedLeaves hashFn sr lr)

/-- Build the salted Merkle tree: hash the salted leaves into a tree using `hashFn`. -/
def buildSaltedTree {s : Skeleton} (hashFn : α → α → α)
    (salts : LeafData α s) (leaves : LeafData α s) : FullData α s :=
  buildMerkleTreeWithHash (saltedLeaves hashFn salts leaves) hashFn

/-- The leaf value used in a salted opening at index `idx` is the salted commitment of the
underlying leaf with its salt. -/
theorem saltedLeaves_get {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idx : SkeletonLeafIndex s) :
    (saltedLeaves hashFn salts leaves).get idx
      = leafCommit hashFn (salts.get idx) (leaves.get idx) := by
  induction idx with
  | ofLeaf =>
    cases salts; cases leaves; rfl
  | ofLeft idxLeft ih =>
    cases salts with
    | internal sl sr =>
      cases leaves with
      | internal ll lr =>
        simp only [saltedLeaves, LeafData.get_internal_ofLeft]
        exact ih sl ll
  | ofRight idxRight ih =>
    cases salts with
    | internal sl sr =>
      cases leaves with
      | internal ll lr =>
        simp only [saltedLeaves, LeafData.get_internal_ofRight]
        exact ih sr lr

/-- **Salted-construction completeness** (fully proven): an honest opening of the salted tree —
the salted leaf commitment at `idx` plus the honest path — verifies against the salted root.
The salted construction is just a Merkle tree over the commitment leaves, so the single-index
`functional_completeness` applies directly. -/
theorem salted_completeness {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idx : SkeletonLeafIndex s) :
    getPutativeRootWithHash idx
      ((saltedLeaves hashFn salts leaves).get idx)
      (generateProof (buildSaltedTree hashFn salts leaves) idx) hashFn
      = (buildSaltedTree hashFn salts leaves).getRootValue := by
  unfold buildSaltedTree
  exact functional_completeness idx (saltedLeaves hashFn salts leaves) hashFn

/-- **Same-salt deterministic binding for salted openings.** If the compression function is
collision-free, two openings at the same index with the same salt, sibling path, and root cannot
reveal different underlying leaf values. This is still the deterministic core only: the
random-oracle collision-probability step remains a separate probabilistic statement. -/
theorem salted_opening_binding_value {s : Skeleton}
    (idx : SkeletonLeafIndex s) (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salt value₁ value₂ rootValue : α) (proof : List.Vector α idx.depth)
    (h₁ : getPutativeRootWithHash idx (leafCommit hashFn salt value₁) proof hashFn
      = rootValue)
    (h₂ : getPutativeRootWithHash idx (leafCommit hashFn salt value₂) proof hashFn
      = rootValue) :
    value₁ = value₂ := by
  have hcommit :
      leafCommit hashFn salt value₁ = leafCommit hashFn salt value₂ :=
    opening_binding idx hashFn hinj
      (leafCommit hashFn salt value₁) (leafCommit hashFn salt value₂) rootValue proof h₁ h₂
  exact (hinj salt value₁ salt value₂ hcommit).2

/-- **Pair-level deterministic binding for salted openings.** If the compression function is
collision-free, two openings at the same index with the same sibling path and root determine the
entire salted opening pair: both the salt and the underlying leaf value are equal.

This is still only the deterministic no-collision implication. The random-oracle step that bounds
the probability of violating the collision-free premise remains separate. -/
theorem salted_opening_binding_pair {s : Skeleton}
    (idx : SkeletonLeafIndex s) (hashFn : α → α → α)
    (hinj : ∀ a b c d, hashFn a b = hashFn c d → a = c ∧ b = d)
    (salt₁ salt₂ value₁ value₂ rootValue : α) (proof : List.Vector α idx.depth)
    (h₁ : getPutativeRootWithHash idx (leafCommit hashFn salt₁ value₁) proof hashFn
      = rootValue)
    (h₂ : getPutativeRootWithHash idx (leafCommit hashFn salt₂ value₂) proof hashFn
      = rootValue) :
    salt₁ = salt₂ ∧ value₁ = value₂ := by
  have hcommit :
      leafCommit hashFn salt₁ value₁ = leafCommit hashFn salt₂ value₂ :=
    opening_binding idx hashFn hinj
      (leafCommit hashFn salt₁ value₁) (leafCommit hashFn salt₂ value₂) rootValue proof h₁ h₂
  exact hinj salt₁ value₁ salt₂ value₂ hcommit

section HidingDefinition

variable [DecidableEq α] [SampleableType α]

/-- The transcript an honest committer publishes when opening a set of indices: the salted root
together with, for each opened index, the salt, the underlying leaf, and the authentication path. -/
def openTranscript {s : Skeleton} (hashFn : α → α → α)
    (salts leaves : LeafData α s) (idxs : List (SkeletonLeafIndex s)) :
    α × List ((i : SkeletonLeafIndex s) × α × α × List.Vector α i.depth) :=
  let tree := buildSaltedTree hashFn salts leaves
  (tree.getRootValue,
    idxs.map (fun i => ⟨i, salts.get i, leaves.get i, generateProof tree i⟩))

/-- **Hiding (indistinguishability definition, SNARGs book §18).** A salted Merkle commitment is
hiding for a fixed opened index set `idxs` if, for *any* two leaf assignments `leaves₁`, `leaves₂`
that agree on the opened positions, the published transcripts are computationally indistinguishable
when the salts are drawn from the salt sampler `sampleSalts`. We phrase indistinguishability as
equality of the induced output distributions of the transcript over the random choice of salts —
the perfect-hiding specialization; a computational version would replace `=` by an
indistinguishability relation.

This is a *definition only*; see the module roadmap for why a proof is out of scope here. -/
def Hiding {s : Skeleton} (hashFn : α → α → α)
    (sampleSalts : OracleComp (spec α) (LeafData α s))
    (idxs : List (SkeletonLeafIndex s)) : Prop :=
  ∀ (leaves₁ leaves₂ : LeafData α s),
    (∀ i ∈ idxs, leaves₁.get i = leaves₂.get i) →
    (sampleSalts >>= fun salts => pure (openTranscript hashFn salts leaves₁ idxs))
      = (sampleSalts >>= fun salts => pure (openTranscript hashFn salts leaves₂ idxs))

end HidingDefinition

end InductiveMerkleTree

/-! ### Axiom audit (issue #119 salted Merkle construction / hiding-definition front doors) -/

#print axioms InductiveMerkleTree.saltedLeaves_get
#print axioms InductiveMerkleTree.salted_completeness
#print axioms InductiveMerkleTree.salted_opening_binding_value
#print axioms InductiveMerkleTree.salted_opening_binding_pair
#print axioms InductiveMerkleTree.openTranscript
#print axioms InductiveMerkleTree.Hiding
